(in-package "ACL2")

(include-book "std/util/defrule" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/typed-lists/top" :dir :system)
(include-book "std/lists/top" :dir :system)
(include-book "std/basic/inductions" :dir :system)

(defun element-equality (low high a)
    (if 
        (or 
            (not 
                (natp 
                    low
                )
            )
            (not 
                (natp 
                    high
                )
            )
        )
        1
        (if 
            (< 
                low 
                high
            )
            (if 
                (= 
                    (nth 
                        low 
                        a
                    ) 
                    (nth 
                        high 
                        a
                    )
                )
                (element-equality 
                    low 
                    (- 
                        high 
                        1
                    ) 
                    a
                )
                0
            )
            1
        )
    )
)