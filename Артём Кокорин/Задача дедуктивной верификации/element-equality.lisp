(in-package "ACL2")

(include-book "std/util/defrule" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/typed-lists/top" :dir :system)
(include-book "std/lists/top" :dir :system)
(include-book "std/basic/inductions" :dir :system)

(defun element-equality-bool(j a)
    (if (not (natp j)) nil
        (if (= 0 j) t
          (and (= (nth (- j 1) a) (nth j a))
              (element-equality-bool (- j 1) a)
          )
        )
    )
)

(defun element-equality(n a)
  (if (element-equality-bool (- n 1) a) 1 0)
)