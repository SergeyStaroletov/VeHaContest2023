(in-package "ACL2")

(include-book "std/util/defrule" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/typed-lists/top" :dir :system)
(include-book "std/lists/top" :dir :system)
(include-book "std/basic/inductions" :dir :system)

(defun element-equality (i j a)
    (if 
        (and
            (natp i)
            (natp j)
            (<= i j)
        )
        (if (= i j)
            1
            (if (= (nth i a) (nth j a))
                (element-equality i (- j 1) a)
                0
            )
        )
        0
    )
)
