#define NUM_MODULES 4
#define BCPU 0
#define BIUSL 1
#define ENGINE 2
#define OTHER 3

#define SetAccelerometers 0
#define StartEngine 1
#define StopEngine 2
#define Reboot 3
#define NullCommand 4
#define EnteringEllepticalOrbit 5
#define StopAccelerometers 6

#define Reset 7

#define AngularVelocity 0
#define Speed 1
#define NullData 2

typedef Data {
  int data_type;
  int data
};

typedef Command {
  int command_type;
};

chan command_channel[4] = [4] of { Command };
chan data_channel[4] = [4] of { Data };

// Указывает какой модуль имеет право на приём/передачу по round-robin
chan currentTurn = [0] of { mtype };

bool needClearChans = false;
bool needReboot = false;

/* флаги для проверки завершился ли процесс моделирования и нужно ли запустить процесс заново */
bool accelerometersStopped = false;
bool engineStoped = false;

inline clearChan(chanName) {
  do
    :: chanName ? [_] -> chanName ? _;
    :: else -> break;
  od
}

/* Проверка на БКУ нужна ли перезагрузка при переполнение данных */
inline CheckIfNeedRestart()
{
    if
    :: 
        len(data_channel[BCPU]) >= (4 - 1) 
        -> command_channel[BCPU] ! Reset;
    :: else -> skip;
  fi
}

inline clearChansAfterResetCommand()
 {
      clearChan(data_channel[BCPU]);
      clearChan(data_channel[BIUSL]);
      clearChan(data_channel[ENGINE]);
      clearChan(data_channel[OTHER]);

      clearChan(command_channel[BCPU]);
      clearChan(command_channel[BIUSL]);
      clearChan(command_channel[ENGINE]);
      clearChan(command_channel[OTHER]);
}

proctype BCU() {
  Data d_;
  Command c_;

  Data dataAngularVelocity; /* данные от БИУС-Л и Двигателя для выхода эпилиптическую орбиту */
  Data dataSpeed;

  printf("Start BCU\n")
  do
  :: atomic {
    currentTurn ? BCPU -> printf("ask BCU");
    CheckIfNeedRestart();
    if
      :: command_channel[BCPU] ?? Reset ->
        printf("Datachannel overload. Restarting...");
        needClearChans = true;
      :: else -> skip;
    fi;

    if
    :: command_channel[BCPU] ? c_ ->
        if 
        ::  c_.command_type == EnteringEllepticalOrbit -> /* Если команда о переходе на эллиптическую орбиту*/
            printf ("EnteringEllepticalOrbit\n")
            Command c1;
            c1.command_type = SetAccelerometers;
            command_channel[BIUSL] ! c1; /* БКУ выдает БИУС-Л команду «Включить акселерометры» */

            Command c2;
            c2.command_type = StartEngine;
            command_channel[ENGINE] ! c2; /* БКУ выдает двигателю команду «Запустить двигатель». */
            printf("Have Sent EnteringEllepticalOrbit\n")
        :: c_.command_type == NullCommand ->
            printf("Readed Null Value!")
            skip;
        fi;

    :: data_channel[BCPU] ?? [dataAngularVelocity] && data_channel[BCPU] ?? [dataSpeed]->
        data_channel[BCPU] ? dataAngularVelocity;
        data_channel[BCPU] ? dataSpeed;

                printf("StopEngine and StopAccelometers")
                Command c3;
                c3.command_type = StopEngine;
                command_channel[ENGINE] ! c3; /* Остановка двигателя */

                Command c4;
                c4.command_type = StopAccelerometers;
                command_channel[BIUSL] ! c4; /* Отключение акселерометров */
    fi;
  }
  od;
}


proctype BIUS_L() {
  Data d_l;
  Command c_l;

  printf("Start BIUS_L\n")

  do
  :: atomic {
        currentTurn ? BIUSL -> printf("ask BIUSL\n");

        if :: needClearChans -> clearChan(command_channel[BIUSL]) /* Перезапуск модуля с очисткой канала */
            printf("Restart BIUS_L")
            needClearChans = false;
           :: else -> skip;
        fi; 

        if 
        :: command_channel[BIUSL] ? c_l ->
            printf("Have read BIUSL command channel\n");
            if
              :: c_l.command_type == SetAccelerometers -> 
              printf("SetAccelerometers command type have been readen\n");
              /* Получив команду «Включить акселерометры», БИУС-Л запускает акселерометры, начинает снимать показания с датчиков. 
              БИУС-Л передает данные об угловой скорости БКУ. */
                  Data d1;
                  d1.data_type = AngularVelocity;
                  data_channel[BCPU] ! d1;
              :: c_l.command_type == StopAccelerometers ->
                printf("StopAccelelometers\n");
                accelerometersStopped = true;
             fi;
          else -> 
            skip;
          fi;
    }
  od;
}

proctype Engine() {
  Command c_e;

  printf("Start Engine\n")
  do
  :: atomic {
    currentTurn ? ENGINE -> {printf("ask Engine")}
    if 
    :: command_channel[ENGINE] ? c_e ->
        if 
            /* Получив команду «Запустить двигатель», двигатель запускается. Двигатель начинает передавать данные о скорости БКУ. */
        :: c_e.command_type == StartEngine ->
          printf("Command StartEngine\n")
          Data d1;
          d1.data_type = Speed;
          data_channel[BCPU] ! d1; /* БКУ выдает двигателю команду «Запустить двигатель» */
        :: c_e.command_type == StopEngine ->
          printf("Stop Engine\n")
          engineStoped = true;
        fi;
    :: else -> skip;
    fi;
    }
  od;
}

proctype OtherModules() {
  Command c_m;

  printf("Start OtherModules\n")
  do
    :: atomic {
      currentTurn ? OTHER -> {printf("ask OtherModules")}
      // как работает другие модули не рассматриваем
    }
  od;
}

proctype RoundRobinPoller() {
  do
  :: atomic {

      if :: 
      engineStoped && accelerometersStopped -> /* За окончание моделирование возьмём состояние когда двигатель остановлен и акселелометр */
      {
        printf("\nRestart Modeling\n")
        clearChansAfterResetCommand();
        // обнуляем переменные
        needClearChans = false;
        needReboot = false;
        engineStoped = false;
        accelerometersStopped = false;

        Command commandOrbit;
        commandOrbit.command_type = EnteringEllepticalOrbit;
        command_channel[BCPU] ! commandOrbit;
      }
      :: 
      else -> skip;
    fi;

    currentTurn ! BCPU
    currentTurn ! BIUSL
    currentTurn ! ENGINE
    currentTurn ! OTHER
  }
  od
}

init {

  Command commandOrbit;
  commandOrbit.command_type = EnteringEllepticalOrbit;
  command_channel[BCPU] ! commandOrbit;

  run BCU();
  run BIUS_L();
  run Engine();
  run OtherModules();
  run RoundRobinPoller();
}

// Всегда если произошла "команда о переходе на эллиптическую орбиту", то когда в будущем должна произойти команда "Включить акселерометры"
// G[p -> Fq]