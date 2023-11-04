#define QUEUE_SIZE 4
#define TARGET_BIUS_ANGLE 5 // Угол, при котором манёвр считается завершенным и отправляются команды на выключение BIUS и ENGINE
#define MAX_SKIP_COUNT 2 // Для оптимизации, максимальное число раундов, когда устройство может быть не готово к приёму/передаче.
#define MAX_SKIP_COUNT_COMMAND 5

#define NIL_bius 0 // передача нуля от выключенного bius


inline clearChan(chanName) {
  do
    :: chanName ? [_] -> chanName ? _;
    :: else -> break;
  od
}

inline resetChanIfAroundLimit(chanData, chanCommand) {
  if
    :: (len(chanData) == (QUEUE_SIZE - 1)) -> chanCommand ! reset;
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

inline countChanEmpty(chanName, skipVar) {
  if
    :: nempty(chanName) -> skipVar++;
    :: empty(chanName) -> skip;
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

chan BIUS_DATA = [QUEUE_SIZE] of { byte };
chan ENGINE_DATA = [QUEUE_SIZE] of { byte };
chan MODULE_DATA = [QUEUE_SIZE] of { byte };

chan BIUS_COMMAND = [QUEUE_SIZE] of { mtype };
chan ENGINE_COMMAND = [QUEUE_SIZE] of { mtype };
chan MODULE_COMMAND = [QUEUE_SIZE] of { mtype };

bool isEngineEnabled = false;
bool isBiusEnabled = false;

bool isBiusEnableCommandSend = false;

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
        ::BIUS_COMMAND ?? [reset] ||
          ENGINE_COMMAND ?? [reset] ||
          MODULE_COMMAND ?? [reset] -> goto finish;
        ::else -> skip;
      fi

      if
        :: MODULE_DATA ? [module_data] -> { MODULE_DATA ? module_data; printf("BKU: MODULE_DATA %e\n", module_data) };
        :: ENGINE_DATA ? [engine_data] -> { ENGINE_DATA ? engine_data; printf("BKU: ENGINE_DATA %e\n", engine_data) };
        :: BIUS_DATA ? [bius_data] -> {
          BIUS_DATA ? bius_data;
          printf("MSC: angle %d\n", bius_data)
          if
            :: (bius_data == TARGET_BIUS_ANGLE) && (simulationState == 1) -> {
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
        :: simulationState == 0 -> START: {
          printf("START LANDING")
          simulationState = 1;
          BIUS_COMMAND ! enable_bius;
          ENGINE_COMMAND ! enable_engine;
          isBiusEnableCommandSend = true;
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
  byte skipCount = 0;
  byte skipCountCommand = 0;

  do
  :: atomic {
    currentTurn ? bius -> { printf("BIUS\n"); }

    clearChanAfterResetCommand(BIUS_DATA, BIUS_COMMAND);

    if
      :: BIUS_COMMAND ? [enable_bius] -> {BIUS_COMMAND ? enable_bius; enable = true; isBiusEnabled = true; skipCount = 0; skipCountCommand = 0}
      :: BIUS_COMMAND ? [disable_bius] -> {BIUS_COMMAND ? disable_bius; enable = false; isBiusEnabled = false; skipCount = 0; skipCountCommand = 0}
      :: (skipCount < MAX_SKIP_COUNT) -> skipCount++;
      :: (skipCountCommand < MAX_SKIP_COUNT_COMMAND) -> {
        countChanEmpty(BIUS_COMMAND, skipCountCommand)
        skipCount = 0;
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
  byte skipCount = 0;
  byte skipCountCommand = 0;

  do
  :: atomic {
    currentTurn ? engine -> { printf("ENGINE\n"); }

    clearChanAfterResetCommand(ENGINE_DATA, ENGINE_COMMAND);

    if
      :: ENGINE_COMMAND ? [disable_engine] -> { ENGINE_COMMAND ? disable_engine; enable = false; isEngineEnabled = false; skipCount = 0; skipCountCommand = 0;};
      :: ENGINE_COMMAND ? [enable_engine] -> { ENGINE_COMMAND ? enable_engine; enable = true; isEngineEnabled = true; skipCount = 0; skipCountCommand = 0;};
      :: enable && (skipCountCommand < MAX_SKIP_COUNT_COMMAND) -> {
        countChanEmpty(ENGINE_COMMAND, skipCountCommand)
        if
          :: true -> ENGINE_DATA ! 1; skipCount = 0;
          :: (skipCount < MAX_SKIP_COUNT) -> skipCount++;
        fi
      };
      :: else -> skip;
    fi
  }
  od
}

active proctype MODULE() {
  byte skipCount = 0;

  do
    :: atomic {
      currentTurn ? module -> { printf("MODULE\n"); }

      clearChanAfterResetCommand(MODULE_DATA, MODULE_COMMAND);

      if
        :: MODULE_COMMAND ? _ -> { skip; skipCount = 0 }
        :: true -> { MODULE_DATA ! 1; skipCount = 0  }
        :: (skipCount < MAX_SKIP_COUNT) -> skipCount++;
      fi
    }
  od
}

// Есть шанс, что если мы начнём манёвр, то мы его корректно закончим
ltl p1 { ((simulationState == 1) -> <> (simulationState == 3 && !isEngineEnabled && !isBiusEnabled)) };

// Но не ВСЕГДА (верификация завершается ошибкой с контрпримером)
ltl p2 { [] ((simulationState == 1) -> <> (simulationState == 3 && !isEngineEnabled && !isBiusEnabled)) };

// Всегда если команда на включение BIUS была отправлена, то он включится. Тот самый баг из описания. Демонстрирует как команда reset перебивает команду enable_bius
ltl p3 { [] ((isBiusEnableCommandSend && simulationState == 1) -> <> isBiusEnabled) };
