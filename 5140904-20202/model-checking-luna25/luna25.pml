#define COMMAND_BKU 1
#define COMMAND_BIUS 2
#define COMMAND_ENGINE 3

#define COMMAND_MAX_SIZE 3

#define NULL_ANGLE 0
#define MAX_ANGLE 5

mtype = {start_bius, reset_bius, finish_bius, start_engine, finish_engine, start_bku, bku_start_all, bku_finish_all, finish_bku}

chan bku_data = [COMMAND_MAX_SIZE] of {byte};
chan bku_engine_command = [COMMAND_MAX_SIZE] of {mtype};
chan bku_bius_command = [COMMAND_MAX_SIZE] of {mtype};

chan engine_command = [COMMAND_MAX_SIZE] of {mtype};

chan bius_command = [COMMAND_MAX_SIZE] of {mtype};
chan bius_data = [COMMAND_MAX_SIZE] of {byte};

mtype bkuGlobalState = start_bku;
bool isEngineEnabled = false;
bool isBiusEnabled = false

active proctype bku() {
    mtype currentState = start_bku;
    byte data;
    byte skipNull = 0;

    do 
        :: currentState == start_bku -> {
            currentState = bku_start_all;
            bkuGlobalState = bku_start_all;
            bku_bius_command ! start_bius;
            bku_engine_command ! start_engine;
            printf("enter hereeee");
        } 
        :: currentState == bku_start_all && (bku_data ? [data]) -> {
            bku_data ? data;
    
            if 
                :: (data >= MAX_ANGLE) -> {
                    printf("enter into max angle")
                    currentState = bku_finish_all;
                    bkuGlobalState = bku_finish_all;
                    bku_bius_command ! finish_bius;
                    bku_engine_command ! finish_engine;
                }
                :: (data == NULL_ANGLE) -> {
                    skipNull++;
                }
                :: (skipNull == COMMAND_MAX_SIZE && len(bku_data) == COMMAND_MAX_SIZE - 1) -> {
                    skipNull = 0;
                    bku_bius_command ! reset_bius;
                }
            fi
        }
        :: currentState == bku_finish_all -> {
            currentState = finish_bku;
            bkuGlobalState = finish_bku;
        }
        :: currentState == finish_bku -> {
            break;
        }
    od
}

active proctype bius() {
    mtype command;
    byte angle = 0;

    do
        :: bius_command ? [command] -> {
            bius_command ? command;
            if 
                :: command == start_bius -> {
                    isBiusEnabled = true;
                }
                :: command == finish_bius -> {
                    isBiusEnabled = false;
                }
                :: command == reset_bius -> {
                    byte data;
                    printf("reset bius")
                    // isBiusEnabled = false
                    do
                        ::(bius_command ? [command]) -> bius_command ? command;
                        ::!(bius_command ? [command]) -> {
                            printf("Bius command clear");
                            break
                        }
                    od
                    do 
                        ::(bku_data ? [data]) -> bku_data ? data;
                        ::!(bius_command ? [command]) -> break;
                    od
                    // do 
                    //      ::(bius_data ? [data]) -> bius_data ? data;
                    //      ::!(bius_data ? [data]) -> {
                    //         printf("Bius data clear");
                    //         break
                    //     }
                    // od
                }
            fi
        }
        :: !(bius_command ? [command]) -> {
            byte data;
            if 
                :: !isBiusEnabled && len(bius_data) == COMMAND_MAX_SIZE -> {
                    skip
                }
                :: isBiusEnabled && len(bius_data) < COMMAND_MAX_SIZE -> {
                    if 
                        :: isEngineEnabled -> {
                            angle = MAX_ANGLE;
                        }
                    fi
                    bius_data ! angle;
                }
                :: !(isBiusEnabled) && len(bius_data) < COMMAND_MAX_SIZE -> {
                    bius_data ! NULL_ANGLE;
                }
                :: else -> skip
            fi
        }
        :: bkuGlobalState == finish_bku -> {
            break
        }
    od
}

active proctype engine() {
    mtype command;

    do
        :: (engine_command ? [command]) -> {
            engine_command ? command;
            if 
                :: command == start_engine -> {
                    isEngineEnabled = true;
                }
                :: command == finish_engine -> {
                    isEngineEnabled = false;
                }
            fi
        }
        :: bkuGlobalState == finish_bku -> {
             break
        }
    od
}


active proctype bus() {
    byte currentCommand = COMMAND_BKU;
    
    do :: atomic {
            len(bku_bius_command) != 0 || len(bku_engine_command) != 0 || len(bius_data) != 0

            if 
                :: currentCommand == COMMAND_BKU -> {
                    mtype command1;
                    mtype command2;
                    if
                        :: bku_engine_command ? [command1] && len(engine_command) < COMMAND_MAX_SIZE -> {
                            bku_engine_command ? command1;
                            if 
                                :: command1 == start_engine -> {
                                    engine_command ! command1;
                                }
                                :: command1 == finish_engine -> {
                                    engine_command ! command1;
                                }
                            fi
                        }
                        ::  bku_bius_command ? [command2] && len(bius_command) < COMMAND_MAX_SIZE -> {
                            bku_bius_command ? command2;
                            if 
                                :: command2 == start_bius -> {
                                    bius_command ! command2;
                                }
                                :: command2 == finish_bius -> {
                                    bius_command ! command2;
                                }
                                :: command2 == reset_bius -> {
                                    bius_command ! command2;
                                }
                            fi
                        }
                        :: len(bku_bius_command) == 0 && len(bku_engine_command) == 0 -> {
                            skip
                        }
                    fi
                    currentCommand = COMMAND_BIUS
                }
                :: currentCommand == COMMAND_BIUS -> {
                    byte data;
                        if 
                            :: (bius_data ? [data] && len(bku_data) < COMMAND_MAX_SIZE) -> {
                                bius_data ? data
                                bku_data ! data
                            }
                            :: !(bius_data ? [data]) -> {
                                skip
                            }
                        fi
                    currentCommand = COMMAND_ENGINE;
                }
                :: currentCommand = COMMAND_ENGINE -> {
                    currentCommand = COMMAND_BKU;
                }
            fi
        }
        :: bkuGlobalState == finish_bku -> {
            break
        }
    od
        
}

ltl p1 { (bkuGlobalState == bku_start_all) -> <> (bkuGlobalState == finish_bku) };