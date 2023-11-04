#define LANDING_TIME 10                 // Time to changing round orbit to eliptic  
#define UNIVERSE_CRASH_TIME 50          // Constant time for ending simulation

int time = 0;                           // Time flow valiable       
int who_is_active[4] = {0, 0, 0, 0};    // Round-Robin controller
// :::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::


// :::::::::::::::::::::::::::::::::: BUS ::::::::::::::::::::::::::::::::::
// Emergency reboot BIUS field
bool reboot_BIUS = 0; 
// DATA CHANNELS
chan from_BIUS = [5] of {int}; 
chan from_Engine = [5] of {int};
chan from_Others = [5] of {int};
// COMMAND CHANNELS
chan to_BIUS = [5] of {int};
chan to_Engine = [5] of {int};
chan to_Others = [5] of {int};
// :::::::::::::::::::::::::::::::::: BUS ::::::::::::::::::::::::::::::::::


// MODULE STATUS
bool Engine_work = 0;
bool BIUS_working=0;



// :::::::::::::::::::::::::::::::::: BKU ::::::::::::::::::::::::::::::::::
active proctype BKU() {
    int zeros = 0; // 
    do
    :: who_is_active[0] -> {
        printf("[BKU] Time: %d\n", time);
        time++; // simulating global time flow (one cycle - one time step)
        if
        :: time == UNIVERSE_CRASH_TIME -> { // End of simulation
            who_is_active[0] = 0;
            break;
        }
        :: time == LANDING_TIME -> { // Begin change of orbit process
            printf("[BKU] Sending commands, start to changing orbit...\n");
            to_BIUS ! 1;
            to_Engine ! 1;
            who_is_active[0] = 0;
            who_is_active[1] = 1;
        }
        :: else -> { // Default actions
            zeros = 0;
            // ::::::::::: READ DATA :::::::::::
            printf("[BKU] Start reading data..\n");
            printf("[BKU] Listen BIUS channel..\n");
            do 
            :: len(from_BIUS) != 0 -> {
                printf("Reading from BIUS\n");
                int m;
                from_BIUS ? m;
                // very intelligence analisys
                if
                :: m == 0 -> {
                    zeros++;
                }
                :: else -> {
                    skip;
                }
                fi
            }
            :: else -> { break; }
            od
            if
            :: zeros == 5 -> { // Emergency reboot
                reboot_BIUS = 1;
                printf("[BKU] Bus overflow... send reboot to BIUS\n");
            }
            :: else -> {
                skip;
            }
            fi
            
            printf("[BKU] Listen Engine channel..\n");
            do
            :: len(from_Engine) != 0 -> {
                int m;
                from_Engine ? m;
                // getting speed values
            }
            :: else -> { break; }
            od
            
            printf("[BKU] Listen Others Modules channel..\n");
            do
            :: len(from_Others) != 0 -> {
                int m;
                from_Others ? m;
                // Reading data from Others Modules
                // ...don't care
            }
            :: else -> { break; }
            od
            // ::::::::::: READ DATA :::::::::::

            to_BIUS ! 2; // ASK DATA FROM BIUS

            // Changing control flow
            who_is_active[0] = 0;
            who_is_active[1] = 1;
        }
        fi
    } 
    // END SIMMULATION TERMINTATION
    :: else -> {
        if
        :: time == UNIVERSE_CRASH_TIME -> {
            break;
        }
        :: else -> {
            skip;
        }
        fi
    }
    od
}
// :::::::::::::::::::::::::::::::::: BKU ::::::::::::::::::::::::::::::::::


// :::::::::::::::::::::::::::::::::: BIUS ::::::::::::::::::::::::::::::::::
active proctype BIUS() {
    int value = 4;
    do
    :: who_is_active[1] -> {
        printf("[BIUS] Time: %d\n", time);
        if 
        :: reboot_BIUS -> { // EMERGENCY REBOOT
            do
            :: len(to_BIUS) != 0 -> { // Command Flush
                to_BIUS ? _;
            }
            :: else -> { break; }
            od
            reboot_BIUS = 0;
        }
        :: else -> {
            do
            :: len(to_BIUS) != 0 -> {
                printf("[BIUS] Listen command chanel...")
                int m;
                to_BIUS ? m;
                if
                :: m == 1 -> {
                    printf("[BIUS] Swithcing on Satus:");
                    int i;
                    select(i : 1 .. 10);
                    if
                    :: i > 1 -> { // ERROR
                        BIUS_working = 1;
                        printf("SUCCESS\n");
                    }
                    :: else -> {printf("FAILED\n");}
                    fi
                }
                :: m == 0 -> {
                    printf("[BIUS] Swithcing off Satus:SUCCESS\n");
                    BIUS_working = 0;
                }
                :: m == 2 -> {
                    printf("[BIUS] Send data to BKU...\n");
                    if
                    :: BIUS_working -> {
                        from_BIUS ! value;
                    }
                    :: else -> {
                        from_BIUS ! 0;
                    }
                    fi
                }
                :: else -> {skip;}
                fi
            }
            :: else -> { break; }
            od
        }
        fi
        // Changing control flow
        who_is_active[1] = 0;
        who_is_active[2] = 1;
    }
     // END SIMMULATION TERMINTATION
    :: else -> {
        if
        :: time == UNIVERSE_CRASH_TIME -> {
            break;
        }
        :: else -> {
            skip;
        }
        fi
    }
    od
}
// :::::::::::::::::::::::::::::::::: BIUS ::::::::::::::::::::::::::::::::::


// :::::::::::::::::::::::::::::::::: ENGINE ::::::::::::::::::::::::::::::::::
active proctype Engine() {
    int Orbital_speed = 100;
    do
    :: who_is_active[2] -> {
        printf("[ENGINE] Time: %d\n", time);
        
        // :::::::: READING COMMANDS ::::::::
        printf("[ENGINE] Start reading commands...\n");
        do
        :: len(to_Engine) != 0 -> {
            int m;
            to_Engine ? m;
            if
            :: m == 1 -> {
                printf("[ENGINE] Turn on\n");
                Engine_work = 1;
            }
            :: else -> {
                printf("[ENGINE] Turn off\n");
                Engine_work = 0;
            }
            fi
        }
        :: else -> { break; }
        od
        // :::::::: READING COMMANDS ::::::::
        
        // :::::::: WRITING DATA ::::::::
        
        printf("[ENGINE] Start writing data off\n");
        if
        :: Engine_work == 1 -> {
            from_Engine ! Orbital_speed;
            printf("[ENGINE] Write back linear speed...\n");
        }
        :: else -> {
            skip;
        }
        fi
        
        
        if
        :: Orbital_speed > 0 && Engine_work -> {// Engine is working -> slowing down
            Orbital_speed--;
        }
        :: else -> {skip;}
        fi
        // Changing control flow
        who_is_active[2] = 0;
        who_is_active[3] = 1;
    }
    // END SIMMULATION TERMINTATION
    :: else -> {
            if
            :: time == UNIVERSE_CRASH_TIME -> {
                break;
            }
            :: else -> {
                skip;
            }
            fi
        }
        od
}
// :::::::::::::::::::::::::::::::::: ENGINE ::::::::::::::::::::::::::::::::::


// :::::::::::::::::::::::::::::::::: OTHERS ::::::::::::::::::::::::::::::::::
active proctype Others() {
    do
    :: who_is_active[3] -> {
        printf("[OTHER MODULES] Time:%d\n",time);

        // ::::::::::: WRITING DATA :::::::::::
        int i;
        select(i : 1 .. 10);
        if
        :: i <= 6 -> {
            printf("[OTHER MODULES] Wiriting data to BKU...\n");
            from_Others ! i;
        }
        :: else -> {skip;}
        // ::::::::::: WRITING DATA :::::::::::

        fi
        // Changing control flow
        who_is_active[3] = 0;
        who_is_active[0] = 1;
    }
    // END SIMMULATION TERMINTATION
    :: else -> {
        if
        :: time == UNIVERSE_CRASH_TIME -> {
            break;
        }
        :: else -> {
            skip;
        }
        fi
    }
    od
}
// :::::::::::::::::::::::::::::::::: OTHERS ::::::::::::::::::::::::::::::::::


ltl success_landing{<>[](Engine_work && BIUS_working)};

init { // Initializing round-robin process
    who_is_active[0] = 1;
}
