mtype:state = { CIRCULAR, TRANSITIONAL, ELLIPTICAL, CRASH }

mtype:engine_commands = { START_ENGINE, STOP_ENGINE }
mtype:bius_commands   = { RESTART_BIUS, START_BIUS, STOP_BIUS }

mtype:speed = { SPEED_AT_CIRCULAR, SPEED_AT_TRANSITION, SPEED_AT_ELLIPTICAL, SPEED_AT_CRASH }
mtype:acc   = { ACC_AT_CIRCULAR, ACC_AT_TRANSITION, ACC_AT_ELLIPTICAL, ACC_AT_CRASH }

mtype:modules = { BKU, BIUS, ENGINE }

mtype:bius_state   = { BIUS_ON, BIUS_OFF }
mtype:engine_state = { ENGINE_ON, ENGINE_OFF }

chan engine_commands_chan = [1] of { mtype:engine_commands }
chan bius_commands_chan   = [1] of { mtype:bius_commands }

chan engine_data_chan = [1] of { mtype:speed }
chan bius_data_chan   = [1] of { mtype:acc }

chan schedule = [0] of { mtype:modules }

// state at the start of simulation
mtype:state global_state = CIRCULAR 
mtype:bius_state bius_state = BIUS_OFF
mtype:engine_state engine_state = ENGINE_OFF


// time
int t = 0 
// point in time when the transition from circular to elliptical orbit has started
int trasition_started = -1 
// time needed for the said transition
int TRANSITION_TIME = 20 
// max time that the spacescaft can take on the elliptical orbit before distorting its trajectory completely
int ADMISSIBLE_DELTA_T = 7

// time_step() simulates time steps and controls the global_state
inline time_step() {
    t++
    if
        :: (global_state == CIRCULAR) && 
                (trasition_started > -1) -> 
            global_state = TRANSITIONAL
        :: (global_state == TRANSITIONAL) && 
                (t - trasition_started > TRANSITION_TIME) -> 
            global_state = ELLIPTICAL
        :: (global_state == ELLIPTICAL) && 
                (t - trasition_started > TRANSITION_TIME + ADMISSIBLE_DELTA_T) && 
                (engine_state == ENGINE_ON) -> 
            global_state = CRASH
        :: else -> skip
    fi
}

// assume all modules take approximately same time to read and write their data (1 time unit)
// reading and writing is intended to be non-blocking
active proctype time() {
    do
        :: atomic {
            schedule ! BKU
            time_step()
            schedule ! BIUS
            time_step()
            schedule ! ENGINE
            time_step()
        }
    od
}


active proctype bku() {
    // state according to BKU
    mtype:state bku_state = CIRCULAR
    mtype:speed v
    mtype:acc   a

    do
        :: schedule ? BKU -> atomic {
            // recieve data
            do 
                :: engine_data_chan ? [v] -> engine_data_chan ? v
                :: bius_data_chan ? [a] -> bius_data_chan ? a
                :: else -> break
            od

            // send commands
            if 
                :: global_state != CRASH && bku_state == CIRCULAR -> {
                    bku_state = TRANSITIONAL
                    engine_commands_chan ! START_ENGINE
                    bius_commands_chan ! START_BIUS
                }
                :: global_state != CRASH && bku_state == TRANSITIONAL -> {
                    if 
                        :: (a == ACC_AT_ELLIPTICAL) && (v == SPEED_AT_ELLIPTICAL) -> {
                            bku_state = ELLIPTICAL
                            engine_commands_chan ! STOP_ENGINE
                            bius_commands_chan ! STOP_BIUS
                        }
                        :: else -> skip
                    fi
                }
                :: global_state != CRASH && bku_state == ELLIPTICAL -> {
                        skip
                }
            fi
        }
    od
}


active proctype bius() {

    mtype:bius_commands bius_command
    mtype:acc           bius_data

    do
        :: schedule ? BIUS -> atomic {
            // receive a command if it exists
            if
                :: bius_commands_chan ? [bius_command] -> {
                    bius_commands_chan ? bius_command
                    if
                        :: bius_command == START_BIUS -> bius_state = BIUS_ON
                        :: bius_command == RESTART_BIUS -> skip // TODO: make bius_commands_chan empty
                        :: bius_command == STOP_BIUS -> bius_state = BIUS_OFF
                    fi
                }
                :: else -> skip
            fi
            // send data
            if
                :: bius_state == BIUS_ON -> {
                    if
                        :: global_state == CIRCULAR     -> bius_data = ACC_AT_CIRCULAR
                        :: global_state == TRANSITIONAL -> bius_data = ACC_AT_TRANSITION
                        :: global_state == ELLIPTICAL   -> bius_data = ACC_AT_ELLIPTICAL
                        :: global_state == CRASH        -> bius_data = ACC_AT_CRASH
                    fi
                }
                :: bius_state == BIUS_OFF -> bius_data = ACC_AT_CIRCULAR
            fi
            bius_data_chan ! bius_data
        }
    od
}

active proctype engine() {
    mtype:engine_commands engine_command
    mtype:speed           engine_data

    do
        :: schedule ? ENGINE -> atomic {
            // receive a command if it exists
            if
                :: engine_commands_chan ? [engine_command] -> {
                    engine_commands_chan ? engine_command
                    if
                        :: engine_command == START_ENGINE -> {
                            engine_state = ENGINE_ON
                            trasition_started = t
                        }
                        :: engine_command == STOP_ENGINE -> {
                            engine_state = ENGINE_OFF
                        }
                    fi
                }
                :: else -> skip
            fi
            
            // send data
            if 
                :: global_state == CIRCULAR     -> engine_data = SPEED_AT_CIRCULAR
                :: global_state == TRANSITIONAL -> engine_data = SPEED_AT_TRANSITION
                :: global_state == ELLIPTICAL   -> engine_data = SPEED_AT_ELLIPTICAL
                :: global_state == CRASH        -> engine_data = SPEED_AT_CRASH
            fi
            engine_data_chan ! engine_data
        }
    od
}

// ltl { global_state != CRASH }
