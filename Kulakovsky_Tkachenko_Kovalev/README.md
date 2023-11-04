<a id="anchor"></a>
# Задача по дедуктивной верификации / "Луна-25" 
## Проверка равенства всех приоритетов в массиве команд

### Команда
* Кулаковский Евгений
* Ткаченко Александра
* Ковалев Виктор
---
### Цель
Необходимо написать постусловие программы в файле «element_equality.c», далее создать файл «element-eq.lisp» в котором будет задаваться теория предметной области. После провести автоматическую дедуктивную верификацию данной программы в системе C-lightVer.

---
### Процесс верификации
Для проведения верификации используется система **C-lightVer**. Проверка запускается с помощью следующей команды в командной строке:

```````
C-lightVer.exe <имя_файла.c> <имя_файла.txt> <имя файла ТПО (без расширения .lisp)>
```````

- **<имя_файла.c>** - имя файла с кодом на языке C, в данном случае это файл **«element_equality.c»**;
- **<имя_файла.txt>** - имя файла, который будет создан в рабочей директории с записаным внутрь отчетом по проведенной верификации (имя можно задать любое, например **«report.txt»**);
- **<имя_файла ТПО>** - имя файла с теорией предметной области, пишется без расширения имени файла, в данном случае это файл **element-eq**.

---
### Ожидаемые результаты

После выполнения описанной выше команды, в рабочей директории должны создаться следующие файлы, подтверждающие прохождение верификации:

``````
- element_equality-verification-condition-1.cert
- element_equality-verification-condition-1.lisp
- element_equality-verification-condition-theory.cert
- element_equality-verification-condition-theory.lisp
- element-eq.cert
``````
---
### Постусловие

В файле **«element_equality.c»** уже есть подготовленное предусловие программы, по аналогии с этим и представленным примером **«abs_sum.c»** составлено следующее постусловие:

``````
/* (= (element-eq 0 (- n 1) a) result) */
``````
---
### Теория предметной области
Теория предметной области задается в созданном нами файле **«element-eq.lisp»**

В начале файла необходимо указать следующую преамбулу:

``````lisp
(in-package "ACL2")

(include-book "std/util/defrule" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/typed-lists/top" :dir :system)
(include-book "std/lists/top" :dir :system)
(include-book "std/basic/inductions" :dir :system)
``````

Далее мы определяем функцию **element-eq(i j a)**. 
Код представлен ниже:
```lisp
(defun element-eq(i j a)
    (if (or (not (natp i)) (not (natp j))) 0
        (if (> i j) 0
            (if (= i j) 1
                (if (not (equal (nth (- j 1) a) (nth j a))) 0
                    (element-eq i (- j 1) a)
                )
            )
        )
    )
)
```
[Подняться вверх](#anchor)