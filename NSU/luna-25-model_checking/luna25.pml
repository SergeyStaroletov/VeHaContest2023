#define BKU_DATA_OVERFLOW 200

// BKU
// BIUS-L
// ENGINE
// OTHER_MODULES
// COMMUNICATION PROC

init {
  
  atomic {
    run EVENTS(); // environment

    run BKU();
    run ENGINE();
    run OTHER_MODULES();
    run COMMUNCATION();
    run BIUS_L();
  }
}

chan events_to_bku = [1] of {mtype}

chan data = [250] of {mtype}
chan commands = [250] of {mtype}

chan bius_data_out = [1] of {mtype}
chan bius_command_in = [10] of {mtype}
chan eng_data_out = [1] of {mtype}
chan eng_command_in = [10] of {mtype}
chan other_data_out = [1] of {mtype}
chan other_command_in = [10] of {mtype}

chan bku_command_out = [1] of {mtype}
chan bku_data_in = [1] of {mtype}


// other modules messages
mtype {
  other_modules_some_readings
}
// other modules commands
mtype {
  other_modules_some_command
}



// BIUS-L states
mtype {
 bius_restarting,
 bius_turned_on,
 buis_turned_off // accelerometers are off, 0 is sent instead of real sensor readings
}

// bius_l messages
mtype {
 bius_l_null, // null signal
 bius_l_some_readings,
 bius_l_we_are_on_ellipsis
}
mtype bius_l_state = buis_turned_off;


// environment (or pilot or code) events
mtype {
 env_start,
 env_landing
}
mtype env = env_start;

// BKU commands
mtype {
 bius_l_reboot,
 bius_l_turn_accelerometers_on,
 bius_l_turn_accelerometers_off,
 engine_turn_on,
 engine_turn_off,
 other_modules_command
}

// BKU states
mtype {
  bku_state_idle,
  bku_state_sent_turn_accelerometers_on
}
mtype bku_state = bku_state_idle;

// engine states
mtype {
 eng_turned_on,
 eng_turned_off
}

// engine messages
mtype {
  engine_some_speed,
  engine_i_think_we_are_on_ellispsis
}
mtype engine_state = eng_turned_off;

proctype OTHER_MODULES() {
  do
  // :: true ->
  //   // do nothing
  //   ;
  :: true ->
    other_data_out ! other_modules_some_readings;
  :: other_command_in ?? other_modules_some_command ->
    printf("other modules: executing some command.");
  od
}



proctype EVENTS() {
  int count = 0;
  // busy wait to simulate time before landing
  do
    :: count != 100 ->
      count = count + 1
    :: count == 100 ->
      events_to_bku ! env_landing;
      break
  od
}

proctype BKU() {
  bool engine_ok_for_landing = false;
  bool bius_ok_for_landing = false;

  do
  :: (len(data) > BKU_DATA_OVERFLOW) ->
    // sparious check if buffer has overflown
    printf("check buffer\n");
    bku_command_out ! bius_l_reboot;
  :: events_to_bku ?? env_landing ->
    // landing started
    printf("landing started...")
    bku_command_out ! bius_l_turn_accelerometers_on;
    bku_state = bku_state_sent_turn_accelerometers_on;
    bku_command_out ! engine_turn_on;
    //bku_state = bku_state_idle;
  :: true ->
    // spurious other commands
    bku_command_out ! other_modules_command;
  :: (bius_ok_for_landing && engine_ok_for_landing) ->
    bku_command_out ! engine_turn_off;
    bku_command_out ! bius_l_turn_accelerometers_off;
  :: bku_data_in ?? engine_some_speed ->
    printf("received speed reading from engine");
  :: bku_data_in ?? engine_i_think_we_are_on_ellispsis ->
    engine_ok_for_landing = true;
  :: bku_data_in ?? bius_l_some_readings ->
    printf("received readings from bius l");
  :: bku_data_in ?? bius_l_null ->
    printf("received null signal from bius l");
  :: bku_data_in ?? bius_l_we_are_on_ellipsis ->
    bius_ok_for_landing = true;
  od
}


proctype BIUS_L() {

  int busy_wait_cnt = 0;

  do
    :: bius_l_state == buis_turned_off ->
      bius_data_out ! bius_l_null;
      printf("bius sent null\n");
    :: bius_l_state == bius_turned_on ->
      printf("bius is active\n");
      if
        :: busy_wait_cnt == 20 ->
            bius_data_out ! bius_l_we_are_on_ellipsis;
        :: busy_wait_cnt != 20 ->
            bius_data_out ! bius_l_some_readings;
      fi
    :: bius_command_in ?? bius_l_reboot ->
      printf("bius got command to restart;\n");
      bius_l_state = bius_restarting;
    :: bius_command_in ?? bius_l_turn_accelerometers_off ->
      printf("bius got command to turn off;\n");
      bius_l_state = buis_turned_off;
    :: bius_command_in ?? bius_l_turn_accelerometers_on ->
      printf("bius got command to turn on;\n");
      bius_l_state = bius_turned_on;

    :: bius_l_state == bius_restarting ->
      busy_wait_cnt = 0;
      printf("bius l restarting...");
  od

}


proctype COMMUNCATION() {
  mtype msg;
  do
    ::
      // receive new data
      if
        :: nempty(bius_data_out) ->
          bius_data_out ? msg;
          data ! msg;
      fi
      if
        :: nempty(eng_data_out) ->
          eng_data_out ? msg;
          data ! msg
      fi
      if
        :: nempty(other_data_out) ->
          other_data_out ? msg;
          data ! msg
      fi

      // receive command from BKU
      if
        :: nempty(bku_command_out) ->
          bku_command_out ? msg;
          commands ! msg
      fi
      
      // transmit commands to components
      commands ? msg;
      if
        :: (msg == bius_l_reboot) || (msg == bius_l_turn_accelerometers_on) || (msg == bius_l_turn_accelerometers_off) ->
          bius_command_in ! msg;
      fi
      if :: (msg == engine_turn_on) || (msg == engine_turn_off) ->
          eng_command_in ! msg;
      fi
      if :: (msg == other_modules_command) ->
        other_command_in ! msg;
      fi
  od
}

proctype ENGINE() {
  // engine_status is used here
  //  engine_turn_on,
  //  engine_turn_off,

  // states
  //  eng_turned_on,
  //  eng_turned_off

  int readsCnt = 0;

  do
  :: engine_state == eng_turned_on ->
    printf("engine is currently on\n")
    if
      :: readsCnt >= 20 ->
        eng_data_out ! engine_i_think_we_are_on_ellispsis
      :: readsCnt < 20 ->
        readsCnt++;
        eng_data_out ! engine_some_speed
    fi
  :: engine_state == eng_turned_off ->
    printf("engine is currently off\n")
  :: eng_command_in ?? engine_turn_on ->
    engine_state = eng_turned_on
  :: eng_command_in ?? engine_turn_off ->
    engine_state = eng_turned_off
  od
}

ltl accelerometers {always ((bku_state == bku_state_sent_turn_accelerometers_on) -> (eventually (bius_l_state == bius_turned_on)))}

