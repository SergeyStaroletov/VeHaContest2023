(in-package "ACL2")

(include-book "std/util/defrule" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/typed-lists/top" :dir :system)
(include-book "std/lists/top" :dir :system)
(include-book "std/basic/inductions" :dir :system)

(defun element-equality(i j a)
	(if (or (not (natp i)) (not (natp j)))     		; Check either i and j are not natural
		1 									   		; if true, return 1
		(if(>= i j)							   		; else check i >= j
			1								   		; if true return 1
													; else i < j => can use a[j] == a[j-1]
			(if(= (nth j a) (nth (- j 1) a))   		; Compare a[j] and a[j-1]
				(element-equality i (- j 1) a) 		; if true return recursively on (j-1)'th element 
				0							   		; else elements are not equal => return 0
			)
		)
	)
)
