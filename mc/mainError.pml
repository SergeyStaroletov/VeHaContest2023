#define NUM_MODULES 4
#define FINISH_COUNTER 10
#define ZERO_DATA 0
#define NON_ZERO_DATA 1
#define BUS_SIZE 4

mtype = { IN_CIRLE_ORBIT, GO_TO_ELLIPTICAL_ORBIT, GOING_TO_ELLIPTICAL_ORBIT, IN_ELLIPTICAL_ORBIT}; // положение станции
mtype = { WORK, NOT_WORK}
mtype = { BKU, BIUS, ENGINE, MODULE }; // доступные модули

mtype = { NONE, ENABLE_ACCELEROMETERS, DISABLE_ACCELEROMETERS, START_ENGINE, STOP_ENGINE, RESET }; // команды

mtype STATION_STATE = IN_CIRLE_ORBIT
mtype BIUS_STATE = NOT_WORK
mtype ENGINE_STATE = NOT_WORK

mtype currCommand = NONE
bool enable_transfered = false

// 0 - для двигателя, 1 - для биуса.
chan command_bus[2] = [BUS_SIZE] of { mtype }; // ОТ БКУ К ДВИГАТЕЛЮ(0) И БИУСУ(1)
chan data_bus[2] = [BUS_SIZE] of { byte } // ОТ ДВИГАТЕЛЮ(0) И БИУСА(1) К БКУ
chan turn = [1] of { mtype };

int angleSpeed = 0;

active proctype Enviroment() {
    do
    :: atomic { 
        turn ! BKU
        turn ! BIUS
        turn ! ENGINE
    }
    od
}

active proctype Bku() {
    int counter = 0;
    int var = 0;
    do 
    :: atomic { 
        turn ? BKU ->
            if 
                ::  STATION_STATE == GO_TO_ELLIPTICAL_ORBIT -> {
                        command_bus[1] ! ENABLE_ACCELEROMETERS;
                        enable_transfered = true;
                        command_bus[0] ! START_ENGINE;
                        STATION_STATE = GOING_TO_ELLIPTICAL_ORBIT;
                }
                :: counter == FINISH_COUNTER -> 
                        command_bus[1] ! DISABLE_ACCELEROMETERS
                        command_bus[0] ! STOP_ENGINE
                :: data_bus[1] ? var -> 
                        counter = counter + var;
                        if 
                            :: counter == FINISH_COUNTER ->
                                ENGINE_STATE = STOP_ENGINE
                                BIUS_STATE = DISABLE_ACCELEROMETERS
                                STATION_STATE = IN_ELLIPTICAL_ORBIT
                                counter = 0;
                        fi
                :: full(data_bus[1]) -> 
                        BIUS_STATE = RESET;
                :: true -> skip;
            fi;
    }
    od;
}

active proctype Bius() {
    do
    :: atomic { 
        turn ? BIUS ->
            if 
                :: command_bus[1] ? ENABLE_ACCELEROMETERS ->
                    BIUS_STATE = WORK
                    data_bus[1] ! NON_ZERO_DATA
                :: command_bus[1] ? DISABLE_ACCELEROMETERS ->
                        BIUS_STATE = NOT_WORK
                :: BIUS_STATE == NOT_WORK ->
                        data_bus[1] ! ZERO_DATA;
                :: BIUS_STATE == WORK ->
                        data_bus[1] ! NON_ZERO_DATA
                :: command_bus[1] ? RESET ->
                    do
                        :: full(command_bus[1]) ->
                            command_bus[1] ? _;
                    od;
                :: true -> skip
            fi
        }
    od;
}

active proctype Engine() {
    do 
    :: atomic{
        turn ? ENGINE ->
            if
                ::  command_bus[0] ? START_ENGINE ->
                        ENGINE_STATE = WORK
                        data_bus[0] ! NON_ZERO_DATA 
                :: command_bus[0] ? STOP_ENGINE ->
                        ENGINE_STATE = NOT_WORK
                :: ENGINE_STATE == WORK ->
                        data_bus[0] ! NON_ZERO_DATA
                :: true -> skip
            fi
        }
    od
}



init {
    printf("Start");
    
}

// ltl { []((BIUS_STATE == RESET && enable_transfered == true) -> []<>(BIUS_STATE == WORK)) }
// ltl { []<>(STATION_STATE == IN_ELLIPTICAL_ORBIT) }
