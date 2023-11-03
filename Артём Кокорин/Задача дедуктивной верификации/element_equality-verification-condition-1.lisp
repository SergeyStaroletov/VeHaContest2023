(in-package "ACL2")

(include-book "std/util/defrule" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/typed-lists/top" :dir :system)
(include-book "std/lists/top" :dir :system)
(include-book "std/basic/inductions" :dir :system)

(include-book "element-equality")

(include-book "element_equality-verification-condition-theory")

(defrule verification-condition-1
    (implies
        (and
            (integer-listp
                a
            )
            (natp
                n
            )
            (<
                0
                n
            )
            (<=
                n
                (length
                    a
                )
            )
        )
        (=
            (element-equality
                n
                a
            )
            (frame-1->result
                (rep-1
                    (-
                        n
                        1
                    )
                    (envir-1-init
                        1
                        a
                    )
                    (frame-1-init
                        1
                        1
                    )
                )
            )
        )
    )
    :rule-classes nil
    :enable
    (
        envir-1-init
        frame-1-init
        rep-1
    )
    :induct
    (dec-induct
        n
    )
)