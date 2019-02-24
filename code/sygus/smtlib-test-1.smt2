(set-option :produce-models true)
(set-option :produce-unsat-cores true)

;; (set-logic QF_S)

;; Combinators -----------------------------------------------------------------

(define-fun head ((s String)) String
  (str.at s 0))

(assert (= (head "x")   "x"))
(assert (= (head "abc") "a"))
(assert (= (head "")    ""))
(check-sat)


(define-fun last ((s String)) String
  (str.at s (- (str.len s) 1)))

(assert (= (last "x")   "x"))
(assert (= (last "abc") "c"))
(assert (= (last "")    ""))
(check-sat)


(define-fun tail ((s String)) String
  (str.substr s 1 (- (str.len s) 1)))

(assert (= (tail "x")   ""))
(assert (= (tail "abc") "bc"))
(assert (= (tail "")    ""))
(check-sat)


(define-fun init ((s String)) String
  (str.substr s 0 (- (str.len s) 1)))

(assert (= (init "x")   ""))
(assert (= (init "abc") "ab"))
(assert (= (init "")    ""))
(check-sat)


(define-fun lowerchar ((c String)) String
  (ite (= c "A") "a"
  (ite (= c "B") "b"
  (ite (= c "C") "c"
  (ite (= c "D") "d"
  (ite (= c "E") "e"
  (ite (= c "F") "f"
  (ite (= c "G") "g"
  (ite (= c "H") "h"
  (ite (= c "I") "i"
  (ite (= c "J") "j"
  (ite (= c "K") "k"
  (ite (= c "L") "l"
  (ite (= c "M") "m"
  (ite (= c "N") "n"
  (ite (= c "O") "o"
  (ite (= c "P") "p"
  (ite (= c "Q") "q"
  (ite (= c "R") "r"
  (ite (= c "S") "s"
  (ite (= c "T") "t"
  (ite (= c "U") "u"
  (ite (= c "V") "v"
  (ite (= c "W") "w"
  (ite (= c "X") "x"
  (ite (= c "Y") "y"
  (ite (= c "Z") "z" c)))))))))))))))))))))))))))

(assert (= (lowerchar "R") "r"))
(check-sat)


(define-fun-rec lower ((s String)) String
  (str.++ (lowerchar (head s)) (lower (tail s))))

(assert (= (lower "John")   "john"))
(assert (= (lower "JOHN")   "john"))
(assert (= (lower "John  ") "john  "))
(check-sat)


;; (define-fun-rec ltrim ((s String)) String
;;   (ite (= " " (head s))
;;     (ltrim (tail s))
;;     s))

;; (assert (= (ltrim "abc")        "abc"))
;; (assert (= (ltrim " abc")       "abc"))
;; (assert (= (ltrim "    abc")    "abc"))
;; (assert (= (ltrim "    abc   ") "abc   "))
;; (check-sat)


;; (define-fun-rec rtrim ((s String)) String
;;   (ite (= " " (last s))
;;     (rtrim (init s))
;;     s))

;; (assert (= (rtrim "abc")        "abc"))
;; (assert (= (rtrim "abc ")       "abc"))
;; (assert (= (rtrim "abc    ")    "abc"))
;; (assert (= (rtrim "    abc   ") "    abc"))
;; (check-sat)


;; (define-fun-rec trim ((s String)) String
;;   (ltrim (rtrim s)))

;; (assert (= (trim "abc")        "abc"))
;; (assert (= (trim " abc")       "abc"))
;; (assert (= (trim "    abc")    "abc"))
;; (assert (= (trim "abc    ")    "abc"))
;; (assert (= (trim "    abc   ") "abc"))
;; (check-sat)


;; ;; Programs --------------------------------------------------------------------

;; (define-fun f1 ((firstname String) (lastname String)) String
;;   (lower (str.++ lastname firstname)))

;; (assert (= (f1 "John" "Doe"   ) "doejohn"  ))
;; (assert (= (f1 "Jane" "Smith" ) "smithjane"))
;; (check-sat)


;; --------------------------------------------------------------------------------

; (define-fun f2 ((firstname String) (lastname String)) String)

; trim(lower(concat(1, 0)))
; (assert (= (f "John   " "  Doe"         ) "doejohn"   ) )
; (assert (= (f "Jane   " "  Smith"       ) "smithjane" ) )
; lower(concat(trim(1), trim(0)))
; (assert (= (f "   John   " "  Doe   "   ) "doejohn"   ) )
; (assert (= (f "   Jane   " "  Smith   " ) "smithjane" ) )

