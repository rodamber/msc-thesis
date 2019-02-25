(set-option :produce-models true)
(set-option :produce-unsat-cores true)

;; (set-logic QF_SLIA)
(set-logic ALL)

;; Combinators -----------------------------------------------------------------

(define-fun head ((s String)) String
  (str.at s 0))

(push)
(assert (= (head "x")   "x"))
(assert (= (head "abc") "a"))
(assert (= (head "")    ""))
(check-sat)
(pop)


(define-fun last ((s String)) String
  (str.at s (- (str.len s) 1)))

(push)
(assert (= (last "x")   "x"))
(assert (= (last "abc") "c"))
(assert (= (last "")    ""))
(check-sat)
(pop)


(define-fun tail ((s String)) String
  (str.substr s 1 (- (str.len s) 1)))

(push)
(assert (= (tail "x")   ""))
(assert (= (tail "abc") "bc"))
(assert (= (tail "")    ""))
(check-sat)
(pop)


(define-fun init ((s String)) String
  (str.substr s 0 (- (str.len s) 1)))

(push)
(assert (= (init "x")   ""))
(assert (= (init "abc") "ab"))
(assert (= (init "")    ""))
(check-sat)
(pop)


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

(push)
(assert (= (lowerchar "R") "r"))
(check-sat)
(pop)


(define-fun lower ((s String)) String
  (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace s "A" "a") "B" "b") "C" "c") "D" "d") "E" "e") "F" "f") "G" "g") "H" "h") "I" "i") "J" "j") "K" "k") "L" "l") "M" "m") "N" "n") "O" "o") "P" "p") "Q" "q") "R" "r") "S" "s") "T" "t") "U" "u") "V" "v") "W" "w") "X" "x") "Y" "y") "Z" "z"))

(push)
(assert (= (lower "John")   "john"))
(assert (= (lower "JOHN")   "john"))
(assert (= (lower "John  ") "john  "))
(check-sat)
(pop)


;; ;; Define trim as an uninterpreted function.
;; (declare-fun trim (String) String)

;; (declare-const spaces (RegEx String))
;; ;; (assert (= spaces (re.* (str.to.re " "))))

;; (assert (forall ((x String)) (not (str.prefixof " " (trim x)))))
;; (assert (forall ((x String)) (not (str.suffixof " " (trim x)))))
;; ;; (assert (forall ((x String)) (str.in.re x (re.++ spaces (str.to.re (trim x)) spaces))))

;; ;; (push)
;; (assert (= (trim "abc")        "abc"))
;; (check-sat)
;; (assert (= (trim " abc")       "abc"))
;; (check-sat)
;; (assert (= (trim "abc ")       "abc"))
;; (check-sat)
;; (assert (= (trim "    abc")    "abc"))
;; (check-sat)
;; (assert (= (trim "abc    ")    "abc"))
;; (check-sat)
;; (assert (= (trim "    abc   ") "abc"))
;; (check-sat)
;; ;; (pop)


;; ;; Programs --------------------------------------------------------------------

(define-fun f1 ((firstname String) (lastname String)) String
  (lower (str.++ lastname firstname)))

(push)
(assert (= (f1 "John" "Doe"   ) "doejohn"  ))
(assert (= (f1 "Jane" "Smith" ) "smithjane"))
(check-sat)
(pop)


;; --------------------------------------------------------------------------------

; (define-fun f2 ((firstname String) (lastname String)) String)

; trim(lower(concat(1, 0)))
; (assert (= (f "John   " "  Doe"         ) "doejohn"   ) )
; (assert (= (f "Jane   " "  Smith"       ) "smithjane" ) )
; lower(concat(trim(1), trim(0)))
; (assert (= (f "   John   " "  Doe   "   ) "doejohn"   ) )
; (assert (= (f "   Jane   " "  Smith   " ) "smithjane" ) )

