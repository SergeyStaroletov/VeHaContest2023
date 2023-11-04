# Model Checking

## Задача формализовать взаимодействие модулей станции "Луна-25" на языке Promela и найти сценарий, приводящий к ошибке, описанной в СМИ.

## Команда
* Алексеев Николай
* Дац Павел
* Субботин Дмитрий

### Задачи
1. Спроектировать взаимодействие компонент, чтобы оно приводило к катастрофе в результате неправильного расположения в пуле данных БИУС-Л команды рапорта значений скорости аппарата. Доказать, что катастрофа может происходить.  
2. Изменить проект так, чтобы избежать катастрофы. Доказать, что катастрофа не может происходить.


## Решение
Созданы процессы для компонентов станции «Луна 25», а именно:
* процесс БКУ (BKU)
* процесс БИУС-Л (BIUSL)
* процесс двигатель (Engine)
* процесс другие модули (Others)

<img src="https://github.com/paveldat/VeHaContest2023/blob/main/FIIT/model-checking/img/1.jpg">

Компоненты обмениваются между собой при помощи каналов команд и каналов данных. Реализована функция clear_channel для защиты от переполнения канала, которая очищает полностью заполненный канал.
Для доказательства того, что катастрофа может происходить были написаны LTL формулы a и b. Формула a показывает: всегда, если отправлена команда «Включить акселерометры», то акселерометры будут включены в будущем. Формула b показывает: всегда, если станция начинает переходить на эллиптическую орбиту, то в будущем станция закончит выход на эллиптическую орбиту и акселерометры будут выключены и двигатель будет выключен. При проверке обоих формул были найдены ошибки, это доказывает, что катастрофа может происходить.
Для исправления данных ошибок был изменен порядок отправки команд в модуле БКУ, при котором команда «Перезагрузка» отправлялась после команды «Включить акселерометры».

```promela
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
```
К сожалению, при проверке формул в исправленной программе были найдены ошибки, поэтому доказать, что катастрофа не может происходить, не получилось.
