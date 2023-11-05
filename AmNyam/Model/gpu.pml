#define SM_COUNT 3
#define WARPS_PER_SM 2
#define SIZE (SM_COUNT * WARPS_PER_SM)

/*
@arg 0 bool: No valid instructions in the warp (eligibility).
@arg 1 int: Next instruction address.
*/
chan warps_out[SIZE] = [1] of { bool, int }

/*
@arg 0 int: First instruction (abstract integer)
@arg 1 int: Second instruction (abstract integer)
*/
chan warps_in[SIZE] = [0] of { int, int }

/*
@arg 0 int: Instruction address
@arg 1 byte: Requesting warp index
*/
chan i_cache_reqs = [0] of { int, byte }

/*
@arg 0 bool: was there a cache hit?
@arg 1 int: First instruction (if hit)
@arg 2 int: Second instruction (if hit)
@arg 3 byte: Requesting warp index
*/
chan sm_in[SM_COUNT] = [1] of { bool, int, int, byte }

proctype sm (byte sm_id; byte warpCount) {
  byte curWarp = 0;
  byte curWarpInd = 0;
  int instrAddr = 0;

  int instr0;
  int instr1;
  bool isHit;
  byte requestingWarp;

  byte i = 0;
  atomic {
    for (i : 0 .. warpCount - 1) {
      run warp(sm_id * SM_COUNT + i);
    }
  }

  do
    :: true -> {
      atomic {
        curWarp = curWarp + 1;
        curWarp = (curWarp == warpCount -> 0 : curWarp);
        curWarpInd = sm_id * SM_COUNT + curWarp;
      }
      // Check that warp is eligible
      warps_out[curWarpInd] ? [true, instrAddr] -> {
        // Get address of the next instruction,
        // but keep in the channel in case of a cache miss
        warps_out[curWarpInd] ? <true, instrAddr>;
        // fetchrequest to i-cache
        i_cache_reqs ! instrAddr, curWarpInd;
        // wait for the response
        sm_in[sm_id] ? isHit, instr0, instr1, requestingWarp;

        // on cache hit
        isHit -> {
          // free the channel
          warps_out[curWarpInd] ? true, instrAddr;
          // propagate instructions to warp
          warps_in[curWarpInd] ! instr0, instr1;
        }
        // on cache miss simply proceed to the next warp
      }
    }
  od
}

proctype warp(byte warpInd) {
  int instrAddr = 0;
  int instructions[2];

  warps_out[warpInd] ! true, instrAddr;
  do
    :: true -> {
      warps_in[warpInd] ? instructions[0], instructions[1];
      warps_out[warpInd] ! false, 0;
      do
        // *execute instructions*
        :: true -> skip
        // Once instructions are *executed*, wait for the scheduler
        :: true -> {
          instrAddr = instrAddr + 2;
          // Declare that warp is eligible
          // (has no valid instructions left)
          atomic {
            nempty(warps_out[warpInd]) -> { warps_out[warpInd] ? _, _; }
            warps_out[warpInd] ! true, instrAddr;
          }
          break;
        }
      od
    }
  od
}

/*
Cache and instructions are simplified:
1. Cache randomly generates hits and misses
2. Instructions are randomintegers (nodecodingand execution)
*/
proctype iCache() {
  int addr;
  byte warpInd;

  do
    :: true -> {
      i_cache_reqs ? addr, warpInd;

      if
        :: true -> { sm_in[warpInd % SM_COUNT] ! true, 2, 3, warpInd; }
        :: true -> { sm_in[warpInd % SM_COUNT] ! true, 4, 5, warpInd; }
        :: true -> { sm_in[warpInd % SM_COUNT] ! false, 0, 0, warpInd; }
      fi
    }
  od
}

init {
  atomic {
    byte i = 0;
    for (i : 0 .. SM_COUNT - 1) {
      run sm(i, WARPS_PER_SM);
    }
    run iCache();
  }
}
