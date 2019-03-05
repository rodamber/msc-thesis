(set-option :produce-models true)

(declare-fun s () String)
(assert (= s "foo bar xxxxxxxxxxxxxxxxxxxxxxxxx abc xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"))

(declare-fun x () Int)
(declare-fun y () Int)

(assert (<= 0 x))
(assert (<= 0 y))
(assert (<= (+ x y) (str.len s)))

(assert (= (str.substr s x y) "abc"))

(check-sat)
(get-model)
