(set-logic SLIA)

;; Combinators -----------------------------------------------------------------

(define-fun head ((s String)) String
  (str.at s 0))

;; Synthesis -------------------------------------------------------------------

;; We want:
;; (define-fun f ((firstname String) (lastname String)) String
;;   (lower (str.++ lastname firstname)))

(synth-fun f ((firstname String) (lastname String)) String
  ((Start String (firstname lastname
                  ;; head Start
                  (str.++ Start Start)))))

(constraint (= (f "John" "Doe") "doejohn"))

(check-synth)
