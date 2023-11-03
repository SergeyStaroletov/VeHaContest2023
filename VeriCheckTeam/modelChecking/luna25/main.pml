#define queueSize 2

mtype = { bku, bius, engine, module }
mtype = { command, data }

// Указывает опрос системы от ШИНЫ по алгоритму round-robin 
chan currentTurn = [0] of { mtype };

chan commandQueue = [queueSize] of { mtype };
chan dataQueue = [queueSize] of { int };

proctype BKU() {
  int dataMsg;
  do
  :: {
    atomic {
      currentTurn ? bku -> { printf("MSC: BKU %d\n", bku); }
      do
        :: nempty(dataQueue) -> {
          dataQueue ? dataMsg;
          printf("BKU receive data %d\n", dataMsg);
        } 
        :: empty(dataQueue) -> break;
      od
    }
  }
  od
}

proctype BIUS() {
  bool enable = false;
  do
  :: {
    atomic {
      currentTurn ? bius -> { printf("MSC: BIUS %d\n", bius); }

      if
        :: enable == true -> skip;
        :: !enable -> {
          if 
            // недетерминировано выбираем отправлять или нет, имитируя НЕГОТОВНОСТЬ модуля
            :: true -> dataQueue ! 0;
            :: true -> skip;
          fi
          
        }
      fi
    }
  }
  od
}

// proctype ENGINE() {
// }

// proctype MODULE() {
//   bool readeSend = false;

// }

proctype BUS() {
  do
  :: {
    currentTurn ! bku
    currentTurn ! bius
    // turn ! engine
    // turn ! module
  }
  od
}

active proctype main() {
  atomic {
    run BUS();
    run BKU();
    run BIUS();
    // run ENGINE();

    // run MODULE();
  }
}
