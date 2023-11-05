#define NUM_COMMANDS 5

mtype = {CMD_TURN_ON_ACCELEROMETERS, CMD_REPORT_VELOCITY, CMD_START_ENGINE, CMD_STOP_ENGINE, CMD_REBOOT_BIUS_L};
chan commandChannel = [NUM_COMMANDS] of { mtype, int };
chan dataChannel = [NUM_COMMANDS] of { mtype, int };
int BIUS_L_dataQueue[NUM_COMMANDS];
int BKU_commandQueue[NUM_COMMANDS];
int engineRunning = 0;

active proctype BKU() {
    int index = 0;

    // Send commands to BIUS-L
    commandChannel!CMD_TURN_ON_ACCELEROMETERS, index;
    commandChannel!CMD_REPORT_VELOCITY, index;
    
    // Wait for data from BIUS-L
    dataChannel?BIUS_L_dataQueue[index];
    
    // Process data to control engine
    if
    :: BIUS_L_dataQueue[index] == 1 -> // Simulate misplaced velocity reporting command
        commandChannel!CMD_START_ENGINE, index; // Incorrectly assuming we have received velocity data
    :: else -> skip;
    fi;

    // Control engine and further commands
    commandChannel!CMD_STOP_ENGINE, index;
    commandChannel!CMD_REBOOT_BIUS_L, index;
}

active proctype BIUS_L() {
    int index = 0;

    // Simulate data processing
    commandChannel?BIUS_L_dataQueue[index];
    
    if
    :: BIUS_L_dataQueue[index] == 0 -> // Simulate misplaced velocity reporting command
        dataChannel!0, index; // Send incorrect data to BKU
    :: else -> skip;
    fi;

    // Receive other commands
    commandChannel?BIUS_L_dataQueue[index];
    dataChannel!BIUS_L_dataQueue[index];
}

active proctype Engine() {
    int index;

    // Control engine based on BKU's commands
    commandChannel?engineRunning, index;
    if
    :: engineRunning == 1 -> skip;
    :: else -> skip;
    fi;
}

init {
    atomic {
        // Start the processes
        run BKU();
        run BIUS_L();
        run Engine();
    }
}
