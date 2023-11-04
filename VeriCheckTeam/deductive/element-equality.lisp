(in-package "ACL2")

(include-book "std/util/defrule" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/typed-lists/top" :dir :system)
(include-book "std/lists/top" :dir :system)
(include-book "std/basic/inductions" :dir :system)

(defun element-equality(n a)
    (if (natp n)      
        (if (< 0 n)
            (if (= (nth n a) (nth (- n 1) a))
                (element-equality (- n 1) a)
                0 ; exit because not equal
            )
            1 ; recursion finished, all equal
        )
        0 ; n not natp    
    )
)
