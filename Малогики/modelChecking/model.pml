#define N 5
#define NULL_SIGNAL 0
#define FINAL_ANGLE_SPEED 5
#define FINAL_SPEED 5
#define COUNT_FOR_LANDING 7

#define COMMAND_TURNING_ON 1
#define COMMAND_TURNING_OFF 2
#define COMMAND_RELOAD 3

#define BIUSL_NUM 0
#define ENGINE_NUM 1
#define BKU_NUM 2

chan biusCommands = [N] of {byte};
chan biusData = [N] of {byte};
chan engineCommands = [N] of {byte};
chan engineData = [N] of {byte};

byte nextComponent = 0; // Номер следующей компоненты для опроса средой

bit isBiuslTurnedOn = 0;  // Включен ли БИУС-Л
bit biusShouldBeReloaded = 0; // Должен ли быть перезагружен БИУС-Л

inline clearChannel(channel) { // Метод для очистки канала при перезагрузке
	byte tmp;
	do
	:: (len(channel) > 0) ->
		channel ? tmp;
	od
}

// Компонент БКУ
active proctype BKU() {
  bit isLanding = 0; // Поступила ли заявка на посадку
  bit isOnOrbit = 0; // Поступили ли данные для перехода на эллиптическую орбиту
  byte angleSpeed;  // Угловая скорость от БИУС-Л
  byte speed;  // Скорость от двигателя
  byte countForLanding = 0; // Счетчик, при увеличении которого до значения COUNT_FOR_LANDING поступает заявка на посадку
  
  do
  :: atomic {
    if 
	:: (countForLanding < COUNT_FOR_LANDING) ->
		countForLanding = countForLanding + 1;
	:: (countForLanding == COUNT_FOR_LANDING && isLanding == 0) -> 
		isLanding = 1;
	fi
  
    // Если наступила очередь опроса БКУ и есть запрос на посадку, а также каналы команд БИУС-Л и двигателя не заполнены,
	// то через каналы оправляем команды включения соответствующим модулям и делаем шаг на следующий по очереди компонент
    if 
	:: (nextComponent == BKU_NUM && isLanding == 1 && len(biusCommands) < N && len(engineCommands) < N) -> {
		biusCommands ! COMMAND_TURNING_ON;
		engineCommands ! COMMAND_TURNING_ON;
		nextComponent = 0;
		isLanding = 0;
	} 
	// Если наступила очередь опроса БКУ и поступили данные для перехода на эллиптическую орбиту, а также каналы команд БИУС-Л и двигателя не заполнены,
	// то через каналы оправляем команды выключения соответствующим модулям и делаем шаг на следующий по очереди компонент
	:: (nextComponent == BKU_NUM && isOnOrbit == 1 && len(biusCommands) < N && len(engineCommands) < N) -> {
		biusCommands ! COMMAND_TURNING_OFF;
		engineCommands ! COMMAND_TURNING_OFF;
		nextComponent = 0;
		isOnOrbit = 0;
	}
	// Если канал данных БИУС-Л заполнен, отправляем модулю БИУС-Л команду для перезагрзки и команду для последующего включения и делаем шаг на следующий по очереди компонент
	:: (len(biusData) >= N) -> {
		biusCommands ! COMMAND_RELOAD;
		biusCommands ! COMMAND_TURNING_ON;
		nextComponent = 0;
	}
	fi
	
	// Если наступила очередь опроса БКУ и каналы команд БИУС-Л и двигателя не заполнены, то через каналы пытаемся получить данные, 
	// при искомых значениях скорости и угловой скорости обновляем значение isOnOrbit и делаем шаг на следующий по очереди компонент
	if
	:: (nextComponent == BKU_NUM && (len(biusData) > 0 || len(engineData) > 0)) -> {
		if
		:: (len(biusData) > 0) -> 
			biusData ? angleSpeed;
		:: (len(engineData) > 0) -> 
			engineData ? speed;
		fi
		
		if
		:: (angleSpeed == FINAL_ANGLE_SPEED && speed == FINAL_SPEED) ->
			isOnOrbit = 1;
		fi
		nextComponent = 0;
	}
	:: (nextComponent == BKU_NUM) -> nextComponent = 0;
	fi
  }
  od
}

// Компонент БИУС-Л
active proctype BIUSL() {
  byte command; // Переменная для чтения команды из канала
  byte angleSpeed = 0; 
  
  do
  :: atomic {
    // Если наступила очередь опроса БИУС-Л и он выключен, а также канал его команд не пуст,
	// то через канал читаем команду, делаем шаг на следующий по очереди компонент, если получили команду включения, обновляем переменные
    if
	:: (isBiuslTurnedOn == 0 && nextComponent == BIUSL_NUM && len(biusCommands) > 0) -> {
		biusCommands ? command;
		nextComponent = nextComponent + 1;
		if 
		:: (command == COMMAND_TURNING_ON) -> {
			isBiuslTurnedOn = 1;
			biusShouldBeReloaded = 0;
		}
		fi
	}
	// Если наступила очередь опроса БИУС-Л и он включен, а также канал его команд не пуст,
	// то через канал читаем команду, делаем шаг на следующий по очереди компонент, если получили команду выключения, обновляем переменную,
	// если получили команду перезагрузки, обновляем переменные, очищаем канал команд БИУС-Л, после чего добавляя сигнал включения
	// (который мог быть утерян во время очищения канала)
	:: (isBiuslTurnedOn == 1 && nextComponent == BIUSL_NUM && len(biusCommands) > 0) -> {
		biusCommands ? command;
	    nextComponent = nextComponent + 1;
		if 
		:: (command == COMMAND_TURNING_OFF) -> 
			isBiuslTurnedOn = 0;
		:: (command == COMMAND_RELOAD) -> {
			angleSpeed = 0;
			isBiuslTurnedOn = 0;
			biusShouldBeReloaded = 1;
			clearChannel(biusCommands);
			biusCommands ! COMMAND_TURNING_ON;
		}
		fi
	}
	fi
	
	// Если наступила очередь опроса БИУС-Л и он выключен, а также канал его данных не заполнен,
	// то передаем нулевой сигнал и делаем шаг на следующий по очереди компонент
	if
	:: (isBiuslTurnedOn == 0 && nextComponent == BIUSL_NUM && len(biusData) < N) -> {
		biusData ! NULL_SIGNAL;
		nextComponent = nextComponent + 1;
	}
	// Если наступила очередь опроса БИУС-Л и он включен, а также канал его данных не заполнен,
	// то передаем значение угловой скорости по каналу и делаем шаг на следующий по очереди компонент, 
	// а также обновляем угловую скорость (считаем, что в этот момент получаем данные от датчика)
	:: (isBiuslTurnedOn == 1 && nextComponent == BIUSL_NUM && len(biusData) < N) -> {
	    nextComponent = nextComponent + 1;
		biusCommands ! angleSpeed;
		if
		:: (angleSpeed < FINAL_ANGLE_SPEED) -> 
			angleSpeed = angleSpeed + 1;
		fi
	}
	fi
	
	// Если наступила очередь опроса БИУС-Л и он не может получить или передать информацию, делаем шаг на следующий по очереди компонент
	if
	:: (nextComponent == BIUSL_NUM) ->
		nextComponent = nextComponent + 1;
	fi
  }
  od
}

// Компонент Двигателя
active proctype Engine() {
  bit isTurnedOn = 0;
  byte command; // Переменная для чтения команды из канала
  byte speed = 0;
  
  do
  :: atomic {
    // Если наступила очередь опроса двигателя и он выключен, а также канал его команд не пуст,
	// то через канал читаем команду, делаем шаг на следующий по очереди компонент, если получили команду включения, обновляем соответствующую переменную
    if
	:: (isTurnedOn == 0 && nextComponent == ENGINE_NUM && len(engineCommands) > 0) -> {
		engineCommands ? command;
		nextComponent = nextComponent + 1;
		if 
		:: (command == COMMAND_TURNING_ON) ->
			isTurnedOn = 1;
		fi
	}
	// Если наступила очередь опроса двигателя и он включен, а также канал его команд не пуст,
	// то через канал читаем команду, делаем шаг на следующий по очереди компонент, если получили команду выключения, обновляем соответствующую переменную
	:: (isTurnedOn == 1 && nextComponent == ENGINE_NUM && len(engineCommands) > 0) -> {
		engineCommands ? command;
	    nextComponent = nextComponent + 1;
		if 
		:: (command == COMMAND_TURNING_OFF) ->
			isTurnedOn = 0;
		fi
	}
	fi
	
	// Если наступила очередь опроса двигателя и он включен, а также канал его данных не заполнен,
	// то передаем значение скорости по каналу и делаем шаг на следующий по очереди компонент, 
	// а также обновляем скорость
	if
	:: (isTurnedOn == 1 && nextComponent == ENGINE_NUM && len(engineData) < N) -> {
	    nextComponent = nextComponent + 1;
		engineData ! speed;
		if
		:: (speed < FINAL_SPEED) -> 
			speed = speed + 1;
		fi
	}
	// Если наступила очередь опроса двигателя и он не может получить или передать информацию, делаем шаг на следующий по очереди компонент
	:: else -> nextComponent = nextComponent + 1;
	fi
  }
  od
}

// Когда-то в будущем наступит постоянно повторяющееся состояние, при котором БИУС-Л должен быть перезагружен, но будет выключен 
ltl rule {<>[]!(isBiuslTurnedOn == 0 && biusShouldBeReloaded == 1)};
