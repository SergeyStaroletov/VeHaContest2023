mtype:modules = {bku, biusl, engine, others}
mtype:commands = {enable, disable, reboot}
mtype:status = {circular, elliptical_start, elliptical_finish}
mtype:status current_status = circular

chan biusl_commands = [20] of {mtype:commands}
chan biusl_data = [20] of {bool}
chan engine_commands = [20] of {mtype:commands}
chan engine_data = [20] of {bool}
chan others_commands = [20] of {mtype:commands}
chan others_data = [20] of {bool}
chan turn = [0] of {mtype:modules}

bool is_biusl_enabled = 0;
bool is_engine_enabled = 0;
bool is_biusl_command_enable_sent = 0;

inline clear_channel(channel) {
   byte temp
   atomic {
      if 
         :: full(channel) -> {
            do
               :: nempty(channel) -> channel ? temp
               :: empty(channel) -> break
            od
         }
         :: nfull(channel) -> skip
      fi 
   }
}

active proctype BKU() {
    bool current_biusl_data;
    bool current_engine_data;
    int N_zeros = 0;
    do
        :: turn ? bku -> 
        atomic {
            if
                :: current_status == circular ->
                if
                    :: true -> current_status = circular
                    :: true -> current_status = elliptical_start                     
                fi
                :: current_status == elliptical_start && is_biusl_enabled == 0 && is_engine_enabled == 0 -> {
                clear_channel(engine_commands)
                engine_commands ! enable;
                clear_channel(biusl_commands)
                biusl_commands ! enable;
                is_biusl_command_enable_sent = 1;
                }               
                :: current_status == elliptical_start && current_engine_data == 1 && current_biusl_data == 1 -> {
                clear_channel(engine_commands)
                engine_commands ! disable;
                clear_channel(biusl_commands)
                biusl_commands ! disable;
                is_biusl_command_enable_sent = 0;
                current_status = elliptical_finish               
                }
                :: else -> skip
            fi
            if
                :: nempty(engine_data) -> engine_data ? current_engine_data
                :: nempty(biusl_data) -> {
                biusl_data ? current_biusl_data
                if
                    :: current_biusl_data == 0 -> N_zeros = N_zeros + 1
                    :: current_biusl_data == 1 -> N_zeros = 0
                    :: else -> skip
                fi
                }
                :: empty(engine_data) && empty(biusl_data) -> skip
            fi         
            if 
                :: N_zeros > 10 -> {
                clear_channel(biusl_commands)
                biusl_commands ! reboot
                N_zeros = 0
                }
                :: else -> skip
            fi
        };
        turn ! biusl;
    od
}

active proctype BIUSL() {
   bool is_biusl_data_ok = 0;
   mtype:commands command;
      do
         :: turn ? biusl -> 
         atomic {
               if
                  :: biusl_commands ? [enable] -> {
                        biusl_commands ? command;
                        is_biusl_enabled = 1;
                  }
                  :: biusl_commands ? [disable] -> {
                        biusl_commands ? command;
                        is_biusl_enabled = 0;
                  }
                  :: biusl_commands ? [reboot] -> {
                        do
                           :: biusl_commands ? command
                           :: empty(biusl_commands) -> break
                        od
                        is_biusl_enabled = 0;
                   }
                  :: else -> skip
               fi;
               if 
                  :: is_biusl_enabled == 1 && is_biusl_data_ok == 0 -> {
                     if
                        :: true -> is_biusl_data_ok = 0;
                        :: true -> is_biusl_data_ok = 1;
                     fi
                  }
                  :: else -> skip
               fi
               clear_channel(biusl_data)
               biusl_data ! is_biusl_data_ok;
            };
         turn ! engine;
      od
}

active proctype Engine() {   
    bool is_engine_data_ok = 0;
    mtype:commands command;
    do
         :: turn ? engine -> 
         atomic {
            if
               :: engine_commands ? [enable] -> {
                     engine_commands ? command;
                     is_engine_enabled = 1;
               }
               :: engine_commands ? [disable] -> {
                     engine_commands ? command;
                     is_engine_enabled = 0;
               }
               :: else -> skip
            fi
            if 
               :: is_engine_enabled == 1 && is_engine_data_ok == 0 -> {
                  if
                     :: true -> is_engine_data_ok = 0;
                     :: true -> is_engine_data_ok = 1;
                  fi
               }
               :: else -> skip
            fi
            if 
               :: clear_channel(engine_data)
               :: is_engine_enabled == 1 -> engine_data ! is_engine_data_ok;
               :: else -> skip
            fi
         }
        turn ! others;
    od
}

active proctype Others() {
   do
      :: turn ? others -> 
      atomic {
         clear_channel(others_data)
         others_data ! 0;
      }
      turn ! bku;
   od
}

init 
{
   turn ! (bku)
}

ltl a {[](is_biusl_command_enable_sent -> <>(is_biusl_enabled))}
ltl b {[](current_status == elliptical_start -> <> (current_status == elliptical_finish && !is_biusl_enabled && !is_engine_enabled))}