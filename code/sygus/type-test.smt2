(set-option :produce-models true)

(declare-fun s () String)
(declare-fun x () Int)

(assert (= x s))

;; (check-sat)
;; (get-model)
