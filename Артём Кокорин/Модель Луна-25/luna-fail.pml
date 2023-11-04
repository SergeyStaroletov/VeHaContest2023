bool is_measurer_on; // определяет, включены ли ускорители
bool is_engine_on; // определяет, включен ли двигатель
bool should_start_landing; // определяет, надо ли начать процедуру посадки
bool is_landing_started; // определяет, запущена ли процедура посадки

#define RELOAD_MEASURER 0 // команда перезагрузки БИУС-Л
#define TURN_OFF_MEASURER 1 // команда выключения БИУС-Л
#define TURN_ON_MEASURER 2 // команда включения БИУС-Л
#define ZERO_SIGNAL 3 // нулевой сигнал от БИУС-Л
#define VELOCITY_SIGNAL 4 // передача текущей скорости от БИУС-Л

// Индексы компонент
#define CONTROLLER 0 // БКУ
#define MEASURER 1 // БИУС-Л

#define CONTROLLER_DATA_QUEUE_SIZE 2
#define CONTROLLER_COMMAND_QUEUE_SIZE 2
#define MEASURER_DATA_QUEUE_SIZE 2
#define MEASURER_COMMAND_QUEUE_SIZE 2

// очередь команд БКУ, ожидающих передачи
chan controller_command_queue = [CONTROLLER_COMMAND_QUEUE_SIZE] of { byte };
// очередь команд, ожидающих обработки, поступивших в БИУС-Л
chan measurer_command_queue = [MEASURER_COMMAND_QUEUE_SIZE] of { byte };

// очередь данных БИУС-Л, ожидающих передачи
chan measurer_data_queue = [MEASURER_DATA_QUEUE_SIZE] of { byte };
// очередь данных, ожидающих обработки, находящаяся в БКУ
chan controller_data_queue = [CONTROLLER_DATA_QUEUE_SIZE] of { byte };

// БКУ - Бортовой комплекс управления
proctype controller() {
    byte data;
    do
    // Если нужно начать посадку
    :: should_start_landing ->
        is_landing_started = true;
        should_start_landing = false;
        controller_command_queue!TURN_ON_MEASURER
    // Если в очереди есть данные
    :: !should_start_landing && controller_data_queue?[data] ->
        controller_data_queue?data; // эта операция всегда executable, так как
        // к очереди имеет доступ на чтение только процесс controller
        if
        // Получен нулевой сигнал
        :: (data == ZERO_SIGNAL) ->
            if
            // Поступило не так уж и много нулевых сигналов
            :: true -> skip
            // При поступлении слишком большого количества нулевых сигналов перезагружаем БИУС-Л
            :: len(controller_command_queue) < CONTROLLER_COMMAND_QUEUE_SIZE -> 
                controller_command_queue!RELOAD_MEASURER
            fi
        :: data != ZERO_SIGNAL -> skip
        fi
    od
}

// БИУС-Л - Блок измерения угловых скоростей - Луна
proctype measurer() {
    byte command;
    do
    // Если есть команды, обрабатываем их
    :: measurer_command_queue?[command] ->
        measurer_command_queue?command;
        if
        :: command == TURN_ON_MEASURER ->
            // Включаем БИУС-Л
            is_measurer_on = true
        :: command == RELOAD_MEASURER ->
            // Перезагружаем БИУС-Л, сбрасывая очереди команд и данных
            do
            // Если очередь команд не пуста, берём команду
            :: !(measurer_command_queue?[command]) -> measurer_command_queue?command
            od
            do
            // Если очередь данных не пуста, берём данные
            :: !(measurer_data_queue?[command]) -> measurer_data_queue?command
            od
        fi
    // Если команд нет, можем передать данные
    :: !(measurer_command_queue?[command]) && (len(measurer_data_queue) < MEASURER_DATA_QUEUE_SIZE) ->
        if
        :: is_measurer_on ->
            // Передаём данные о скорости
            measurer_data_queue!VELOCITY_SIGNAL
        :: !is_measurer_on ->
            // Передаём нулевой сигнал
            measurer_data_queue!ZERO_SIGNAL
        fi
  od
}

// Среда коммуникации
proctype bus() {
    byte component_index = CONTROLLER;

    // Обходим компоненты по кругу
    do
    // Случай БКУ
    :: (component_index == CONTROLLER) ->
        byte command;
        if
        // Если есть команда для передачи, передаём её
        :: controller_command_queue?[command] &&
            len(measurer_command_queue) < MEASURER_COMMAND_QUEUE_SIZE ->
            controller_command_queue?command;
            measurer_command_queue!command
        // А если нет, идём дальше
        :: !(controller_command_queue?[command] &&
            len(measurer_command_queue) < MEASURER_COMMAND_QUEUE_SIZE) ->
            skip
        fi
        component_index = MEASURER

    // Случай БИУС-Л
    :: (component_index == MEASURER) ->
        byte data;
        if
        // Если есть данные для передачи и можем их передать, передаём их
        :: measurer_data_queue?[data] && 
            len(controller_data_queue) < CONTROLLER_DATA_QUEUE_SIZE ->
            measurer_data_queue?data;
            controller_data_queue!data
        // А если нет, идём дальше
        :: !(measurer_data_queue?[data] && 
            len(controller_data_queue) < CONTROLLER_DATA_QUEUE_SIZE) -> skip
        fi
        component_index = CONTROLLER
  od
}

// В некоторый момент должна запуститься процедура посадки
proctype start_landing() {
    should_start_landing = true;
}

init {
    should_start_landing = false;
    is_landing_started = false;
    is_measurer_on = false;
    is_engine_on = false;

    run controller();
    run measurer();
    run bus();
    run start_landing();
}

// Процедура посадки должна начаться
// ltl landing_will_start {<>(is_landing_started == true)}
// БИУС-Л должен запуститься
ltl measurer_will_start {<>(is_measurer_on)}
