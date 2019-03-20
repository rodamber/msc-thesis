;; size02/1.benchmark

;; Program: Replace
;;          ├── Replace
;;          │   ├── StrHole(name='x0')
;;          │   ├── StrHole(name='x1')
;;          │   └── StrHole(name='x2')
;;          ├── StrHole(name='x3')
;;          └── StrHole(name='x4')

(declare-const input-count   Int) (assert (= example-count 5))
(declare-const example-count Int) (assert (= input-count   5))

; Inputs: (select inputs i j) corresponds to the jth input of example i
(declare-const inputs (Array Int Int String)) ; Example Parameter

(assert (= (select inputs 0 0) "hslcy"))
(assert (= (select inputs 0 1) "hslc"))
(assert (= (select inputs 0 2) "dzoi"))
(assert (= (select inputs 0 3) "dzoi"))
(assert (= (select inputs 0 4) "pnhz"))

(assert (= (select inputs 1 0) "txbymtv"))
(assert (= (select inputs 1 1) "xbymt"))
(assert (= (select inputs 1 2) "igih"))
(assert (= (select inputs 1 3) "tigi"))
(assert (= (select inputs 1 4) "nbeq"))

(assert (= (select inputs 2 0) "xwomw"))
(assert (= (select inputs 2 1) "womw"))
(assert (= (select inputs 2 2) "wmww"))
(assert (= (select inputs 2 3) "xwmw"))
(assert (= (select inputs 2 4) "jrhp"))

(assert (= (select inputs 3 0) "mahpgad"))
(assert (= (select inputs 3 1) "hpgad"))
(assert (= (select inputs 3 2) "blbstag"))
(assert (= (select inputs 3 3) "lbsta"))
(assert (= (select inputs 3 4) "rpeq"))

(assert (= (select inputs 4 0) "ehgqlnx"))
(assert (= (select inputs 4 1) "hgql"))
(assert (= (select inputs 4 2) "umzmy"))
(assert (= (select inputs 4 3) "eumz"))
(assert (= (select inputs 4 4) "gbaa"))


; Outputs: (select outputs i) corresponds to the output of example i
(declare-const outputs (Array Int String))

(assert (= (select outputs 0) "pnhzy"))
(assert (= (select outputs 1) "nbeqhv"))
(assert (= (select outputs 2) "jrhpw"))
(assert (= (select outputs 3) "mabrpeqg"))
(assert (= (select outputs 4) "gbaamynx"))

;; Holes:

(declare-const hole00 Int)
(declare-const hole01 Int)
(declare-const hole02 Int)
(declare-const hole03 Int)
(declare-const hole04 Int)

(declare-const hole10 Int)
(declare-const hole11 Int)
(declare-const hole12 Int)
(declare-const hole13 Int)
(declare-const hole14 Int)

(declare-const hole20 Int)
(declare-const hole21 Int)
(declare-const hole22 Int)
(declare-const hole23 Int)
(declare-const hole24 Int)

(declare-const hole30 Int)
(declare-const hole31 Int)
(declare-const hole32 Int)
(declare-const hole33 Int)
(declare-const hole34 Int)

(declare-const hole40 Int)
(declare-const hole41 Int)
(declare-const hole42 Int)
(declare-const hole43 Int)
(declare-const hole44 Int)

(assert
 (and
  (>= hole00 0) (<  hole00 input-count)
  (>= hole01 0) (<  hole01 input-count)
  (>= hole02 0) (<  hole02 input-count)
  (>= hole03 0) (<  hole03 input-count)
  (>= hole04 0) (<  hole04 input-count)

  (>= hole10 0) (<  hole10 input-count)
  (>= hole11 0) (<  hole11 input-count)
  (>= hole12 0) (<  hole12 input-count)
  (>= hole13 0) (<  hole13 input-count)
  (>= hole14 0) (<  hole14 input-count)

  (>= hole20 0) (<  hole20 input-count)
  (>= hole21 0) (<  hole21 input-count)
  (>= hole22 0) (<  hole22 input-count)
  (>= hole23 0) (<  hole23 input-count)
  (>= hole24 0) (<  hole24 input-count)

  (>= hole30 0) (<  hole30 input-count)
  (>= hole31 0) (<  hole31 input-count)
  (>= hole32 0) (<  hole32 input-count)
  (>= hole33 0) (<  hole33 input-count)
  (>= hole34 0) (<  hole34 input-count)

  (>= hole40 0) (<  hole40 input-count)
  (>= hole41 0) (<  hole41 input-count)
  (>= hole42 0) (<  hole42 input-count)
  (>= hole43 0) (<  hole43 input-count)
  (>= hole44 0) (<  hole44 input-count)))

(assert (distinct hole00 hole01 hole02 hole03 hole04))
(assert (distinct hole10 hole11 hole12 hole13 hole14))
(assert (distinct hole20 hole21 hole22 hole23 hole24))
(assert (distinct hole30 hole31 hole32 hole33 hole34))
(assert (distinct hole40 hole41 hole42 hole43 hole44))

;; Lines | Example | Number
(declare-const line00 String)
(declare-const line10 String)
(declare-const line20 String)
(declare-const line30 String)
(declare-const line40 String)

;; Sketch

(assert (= line00
           (str.replace (select inputs 0 hole00)
                        (select inputs 0 hole01)
                        (select inputs 0 hole02))))
(assert (= (select outputs 0)
           (str.replace line00
                        (select inputs 0 hole03)
                        (select inputs 0 hole04))))

(assert (= line10
           (str.replace (select inputs 1 hole10)
                        (select inputs 1 hole11)
                        (select inputs 1 hole12))))
(assert (= (select outputs 1)
           (str.replace line10
                        (select inputs 1 hole13)
                        (select inputs 1 hole14))))

(assert (= line20
           (str.replace (select inputs 2 hole20)
                        (select inputs 2 hole21)
                        (select inputs 2 hole22))))
(assert (= (select outputs 2)
           (str.replace line20
                        (select inputs 2 hole23)
                        (select inputs 2 hole24))))

(assert (= line30
           (str.replace (select inputs 3 hole30)
                        (select inputs 3 hole31)
                        (select inputs 3 hole32))))
(assert (= (select outputs 3)
           (str.replace line30
                        (select inputs 3 hole33)
                        (select inputs 3 hole34))))

(assert (= line40
           (str.replace (select inputs 4 hole40)
                        (select inputs 4 hole41)
                        (select inputs 4 hole42))))
(assert (= (select outputs 4)
           (str.replace line40
                        (select inputs 4 hole43)
                        (select inputs 4 hole44))))


;; Check

(check-sat)
(get-model)
