#define NUM_COMMANDS 5

mtype = {CMD_TURN_ON_ACCELEROMETERS, CMD_REPORT_VELOCITY, CMD_START_ENGINE, CMD_STOP_ENGINE, CMD_REBOOT_BIUS_L, CMD_READY_TO_WORK};
chan commandChannel = [NUM_COMMANDS] of { mtype, int };
chan dataChannel = [NUM_COMMANDS] of { mtype, int };
int BIUS_L_dataQueue[NUM_COMMANDS];
int BKU_commandQueue[NUM_COMMANDS];
int engineRunning = 0;

active proctype BKU() {
    int index = 0;

    // Send commands to other modules to confirm readiness
    commandChannel!CMD_READY_TO_WORK, index;
    commandChannel!CMD_READY_TO_WORK, index;
    
    // Wait for confirmation from other modules
    commandChannel?CMD_READY_TO_WORK, index;
    commandChannel?CMD_READY_TO_WORK, index;

    // Send commands to BIUS-L
    commandChannel!CMD_TURN_ON_ACCELEROMETERS, index;
    
    // Wait for confirmation from BIUS-L
    commandChannel?CMD_READY_TO_WORK, index;

    // Wait for data from BIUS-L
    dataChannel?BIUS_L_dataQueue[index];
    
    // Process data to control engine
    if
    :: BIUS_L_dataQueue[index] == 1 -> // Simulate correct velocity reporting command
        commandChannel!CMD_START_ENGINE, index; // Correctly assuming we have received velocity data
    :: else -> skip;
    fi;

    // Control engine and further commands
    commandChannel!CMD_STOP_ENGINE, index;
    commandChannel!CMD_REBOOT_BIUS_L, index;
}

active proctype BIUS_L() {
    int index = 0;

    // Confirm readiness to work
    commandChannel?CMD_READY_TO_WORK, index;
    commandChannel?CMD_READY_TO_WORK, index;
    
    // Process and correctly place commands
    commandChannel?BIUS_L_dataQueue[index];
    
    if
    :: BIUS_L_dataQueue[index] == 0 -> // Simulate correctly placed velocity reporting command
        dataChannel!1, index; // Send correct data to BKU
    :: else -> skip;
    fi;

    // Confirm readiness to work
    commandChannel!CMD_READY_TO_WORK, index;

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
