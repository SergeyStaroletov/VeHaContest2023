(in-package "ACL2")

(include-book "std/util/defrule" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/typed-lists/top" :dir :system)
(include-book "std/lists/top" :dir :system)
(include-book "std/basic/inductions" :dir :system)

(defun element-equality(i n a)
    (if
        (or
            (not (natp i))
            (not (natp n))
        )
        0            
        (if
            (>= i n)
            1
            (if (= (nth n a) (nth (- n 1) a))
                (element-equality i (- n 1) a)
                0
            )
        )
    )
)
