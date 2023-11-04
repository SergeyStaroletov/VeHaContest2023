#define queueSize 16
#define targetBiusAngle 5
#define NIL_bius 0 // передача нуля от выключенного bius

inline clearChan(chanName) {
  do
    :: chanName ? [_] -> chanName ? _;
    :: else -> break;
  od
}

inline resetChanIfAroundLimit(chanData, chanCommand) {
  if
    :: (len(chanData) == (queueSize - 1)) -> chanCommand ! reset;
    :: else -> skip;
  fi
}

inline clearChanAfterResetCommand(chanData, chanCommand) {
  if
    :: chanCommand ?? [reset] -> {
      chanCommand ?? reset;
      clearChan(chanData);
      clearChan(chanCommand);
    };
    :: else -> skip;
  fi
}

mtype = { bku, bius, engine, module } // типы модулей
mtype = { enable_bius, disable_bius, reset, enable_engine, disable_engine } // команды

// Состояние манёвра:
// 0 - Луна-25 находится на круговой орбите
// 1 - Переход на эллиптическую орбиту
// 2 - Переход на эллиптическую орбиту завершён
// 3 - Луна-25 находится на эллиптической орбите
byte simulationState = 0;

// Указывает какой модуль имеет право на приём/передачу по round-robin
chan currentTurn = [0] of { mtype };

chan BIUS_DATA = [queueSize] of { byte };
chan ENGINE_DATA = [queueSize] of { byte };
chan MODULE_DATA = [queueSize] of { byte };

chan BIUS_COMMAND = [queueSize] of { mtype };
chan ENGINE_COMMAND = [queueSize] of { mtype };
chan MODULE_COMMAND = [queueSize] of { mtype };

bool isEngineEnabled = false;
bool isBiusEnabled = false;

active proctype ROUNDROBIN() {
  do
  :: atomic {
    currentTurn ! bku
    currentTurn ! bius
    currentTurn ! engine
    currentTurn ! module
  }
  od
}


active proctype BKU() {
  byte bius_data;
  byte engine_data;
  byte module_data;

  do
    :: atomic {
      currentTurn ? bku -> printf("BKU\n");
      resetChanIfAroundLimit(BIUS_DATA, BIUS_COMMAND);
      resetChanIfAroundLimit(ENGINE_DATA, ENGINE_COMMAND);
      resetChanIfAroundLimit(MODULE_DATA, MODULE_COMMAND);

      if
        :: MODULE_DATA ? [module_data] -> { MODULE_DATA ? module_data; printf("BKU: MODULE_DATA %e\n", module_data) };
        :: ENGINE_DATA ? [engine_data] -> { ENGINE_DATA ? engine_data; printf("BKU: ENGINE_DATA %e\n", engine_data) };
        :: BIUS_DATA ? [bius_data] -> { 
          BIUS_DATA ? bius_data; 
          printf("MSC: angle %d\n", bius_data)
          if 
            :: bius_data == targetBiusAngle -> {
              ENGINE_COMMAND ! disable_engine;
              BIUS_COMMAND ! disable_bius;
              simulationState = 2;
              goto finish;
            }
            :: else -> skip;
          fi
        };
        :: else -> skip;
      fi

      // Переход на эллиптическую орбиту
      if
        :: simulationState == 0 -> {
          printf("START LANDING")
          simulationState = 1;
          BIUS_COMMAND ! enable_bius;
          ENGINE_COMMAND ! enable_engine;
        }
        :: true -> skip;
      fi

      // Переход на эллиптическую орбиту завершён
      if
        :: simulationState == 2 && !isEngineEnabled && !isBiusEnabled -> {
          simulationState = 3;
        } 
        :: else -> skip;
      fi

      finish: skip;
    }
  od
}

active proctype BIUS() {
  bool enable = false;
  byte angle = 0;

  do
  :: atomic {
    currentTurn ? bius -> { printf("BIUS\n"); }

    clearChanAfterResetCommand(BIUS_DATA, BIUS_COMMAND);
    // if
    //   :: BIUS_COMMAND ?? [reset] -> {
    //     BIUS_COMMAND ?? reset;
    //     clearChan(BIUS_DATA);
    //     clearChan(BIUS_COMMAND);
    //   };
    //   :: else -> skip;
    // fi

    if
      :: BIUS_COMMAND ? enable_bius -> { enable = true; isBiusEnabled = true; }
      :: BIUS_COMMAND ? disable_bius -> { enable = false; isBiusEnabled = false; }
      :: true -> printf("BIUS: SKIP\n");
      :: true -> {
        if 
          :: enable -> {
            if
              :: isEngineEnabled -> { angle++; }
              :: else -> skip;
            fi
            BIUS_DATA ! angle;
          }
          :: !enable -> BIUS_DATA ! NIL_bius;
        fi
      }
    fi
  }
  od
}

active proctype ENGINE() {
  bool enable = false;

  do
  :: atomic {
    currentTurn ? engine -> { printf("ENGINE\n"); }

    clearChanAfterResetCommand(ENGINE_DATA, ENGINE_COMMAND);

    if
      :: ENGINE_COMMAND ? [disable_engine] -> { ENGINE_COMMAND ? disable_engine; enable = false; isEngineEnabled = false; };
      :: ENGINE_COMMAND ? [enable_engine] -> { ENGINE_COMMAND ? enable_engine; enable = true; isEngineEnabled = true; };
      :: enable -> {
        if
          :: true -> ENGINE_DATA ! 1;
          :: true -> skip;
        fi
      };
      :: else -> skip;
    fi
  }
  od
}

active proctype MODULE() {
  do
    :: atomic {
      currentTurn ? module -> { printf("MODULE\n"); }

      clearChanAfterResetCommand(MODULE_DATA, MODULE_COMMAND);
      
      if
        :: MODULE_COMMAND ? _ -> { skip; }
        :: true -> { MODULE_DATA ! 1; }
        :: true -> { skip; }
      fi
    }
  od
}
