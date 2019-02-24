(set-logic SLIA)

;; Synthesis -------------------------------------------------------------------

;; We want:
;; (define-fun f ((firstname String) (lastname String)) String
;;   (str.++ lastname firstname))

(synth-fun f ((firstname String) (lastname String)) String
           ((Start String
            (firstname lastname
                       (str.++ Start Start)))))

(constraint (= (f "John" "Doe") "DoeJohn"))

(check-synth)
