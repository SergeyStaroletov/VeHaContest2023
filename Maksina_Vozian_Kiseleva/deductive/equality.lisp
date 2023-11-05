(in-package "ACL2")

(include-book "std/util/defrule" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/typed-lists/top" :dir :system)
(include-book "std/lists/top" :dir :system)
(include-book "std/basic/inductions" :dir :system)

(defun equality(i j a)
    (if 
        (or 
             (not 
                  (
                  natp i
                  )
             )
            (not 
                 (
                  natp j
                 )
            )
        )
        0
        (if 
            (
              > 
              i 
              j
            )
            0
            (if 
                (
                  = 
                  i 
                  j
                )
                1                
                (if 
                    (
                      = 
                        (
                          nth 
                          i 
                          a
                        ) 
                        (
                          nth 
                          j 
                          a
                        )
                     )
                    (
                      equality i (- j 1) a
                    )
                    0
               )               
           )  
        )
    )
)
