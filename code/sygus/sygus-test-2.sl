(set-logic SLIA)

;; Combinators -----------------------------------------------------------------

(define-fun head ((s String)) String
  (str.at s 0))

(define-fun tail ((s String)) String
  (str.substr s 1 (- (str.len s) 1)))

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

;; No support for recursive functions:
;; (define-fun-rec lower ((s String)) String
;;   (str.++ (lowerchar (head s)) (lower (tail s))))
;; So we use a dumb workaround:
(define-fun lower ((s String)) String
  (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace (str.replace s "A" "a") "B" "b") "C" "c") "D" "d") "E" "e") "F" "f") "G" "g") "H" "h") "I" "i") "J" "j") "K" "k") "L" "l") "M" "m") "N" "n") "O" "o") "P" "p") "Q" "q") "R" "r") "S" "s") "T" "t") "U" "u") "V" "v") "W" "w") "X" "x") "Y" "y") "Z" "z"))

;; Synthesis -------------------------------------------------------------------

;; We want:
;; (define-fun f ((firstname String) (lastname String)) String
;;   (lower (str.++ lastname firstname)))

(synth-fun f ((firstname String) (lastname String)) String
  ((Start String (firstname lastname
                  (lower Start)
                  (str.++ Start Start)))))

(constraint (= (f "John" "Doe") "doejohn"))

(check-synth)
