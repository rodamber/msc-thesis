;; size02/1.benchmark

;; Program: Replace
;;          ├── Replace
;;          │   ├── StrHole(name='x0')
;;          │   ├── StrHole(name='x1')
;;          │   └── StrHole(name='x2')
;;          ├── StrHole(name='x3')
;;          └── StrHole(name='x4')

(define-const input-count Int 5)
(define-const component-count Int 2)
(define-const line-count Int (+ input-count component-count))

;; Component semantics
(define-fun replace-1 ((x String) (y String) (z String)) String
  (str.replace x y z))


(define-fun replace-2 ((x String) (y String) (z String)) String
  (str.replace x y z))

;; Component inputs
(declare-const replace-1-x String)
(declare-const replace-1-y String)
(declare-const replace-1-z String)

(declare-const replace-2-x String)
(declare-const replace-2-y String)
(declare-const replace-2-z String)

;; Component outputs
(declare-const replace-1-output String)
(declare-const replace-2-output String)

;; Program inputs
(declare-const input-1 String)
(declare-const input-2 String)
(declare-const input-3 String)
(declare-const input-4 String)
(declare-const input-5 String)

;; Program output
(declare-const output String)

;; Lines of each input of each component
(declare-const line-replace-1-x Int)
(declare-const line-replace-1-y Int)
(declare-const line-replace-1-z Int)

(declare-const line-replace-2-x Int)
(declare-const line-replace-2-y Int)
(declare-const line-replace-2-z Int)

;; Lines of each output of each component
(declare-const line-replace-1-output Int)
(declare-const line-replace-2-output Int)

;; Lines of the program input
(declare-const line-input-1 Int)
(declare-const line-input-2 Int)
(declare-const line-input-3 Int)
(declare-const line-input-4 Int)
(declare-const line-input-5 Int)

(declare-const line-output Int)

;; Well-formedness constraints
(assert (and (>= line-input-1 0) (< line-input-1 input-count)))
(assert (and (>= line-input-2 0) (< line-input-2 input-count)))
(assert (and (>= line-input-3 0) (< line-input-3 input-count)))
(assert (and (>= line-input-4 0) (< line-input-4 input-count)))
(assert (and (>= line-input-5 0) (< line-input-5 input-count)))

(assert (and (>= line-replace-1-x 0) (< line-replace-1-x line-count)))
(assert (and (>= line-replace-1-y 0) (< line-replace-1-y line-count)))
(assert (and (>= line-replace-1-z 0) (< line-replace-1-z line-count)))

(assert (and (>= line-replace-2-x 0) (< line-replace-2-x line-count)))
(assert (and (>= line-replace-2-y 0) (< line-replace-2-y line-count)))
(assert (and (>= line-replace-2-z 0) (< line-replace-2-z line-count)))

(assert (and (>= line-output input-count) (< line-output line-count)))

(assert (and (>= line-replace-1-output input-count)
             (<  line-replace-1-output line-count)))

(assert (and (>= line-replace-2-output input-count)
             (<  line-replace-2-output line-count)))

(assert (distinct line-replace-1-output
                  line-replace-2-output))

(assert (< line-replace-1-x line-replace-1-output))
(assert (< line-replace-1-y line-replace-1-output))
(assert (< line-replace-1-z line-replace-1-output))

(assert (< line-replace-2-x line-replace-2-output))
(assert (< line-replace-2-y line-replace-2-output))
(assert (< line-replace-2-z line-replace-2-output))

(assert (and (= replace-1-output
                (replace-1 replace-1-x
                           replace-1-y
                           replace-1-z))
             (= replace-2-output
                (replace-2 replace-2-x
                           replace-2-y
                           replace-2-z))))

;; Data flow constraints: equal locations should hold equal variables

(assert
 (and
  (=> (= line-input-1 line-replace-1-x)               (= input-1 replace-1-x))
  (=> (= line-input-1 line-replace-1-y)               (= input-1 replace-1-y))
  (=> (= line-input-1 line-replace-1-z)               (= input-1 replace-1-z))
  (=> (= line-input-1 line-replace-1-output)          (= input-1 replace-1-output))

  (=> (= line-input-1 line-replace-2-x)               (= input-1 replace-2-x))
  (=> (= line-input-1 line-replace-2-y)               (= input-1 replace-2-y))
  (=> (= line-input-1 line-replace-2-z)               (= input-1 replace-2-z))
  (=> (= line-input-1 line-replace-2-output)          (= input-1 replace-2-output))

  (=> (= line-input-1 line-output)                    (= input-1 output))

  (=> (= line-input-2 line-replace-1-x)               (= input-2 replace-1-x))
  (=> (= line-input-2 line-replace-1-y)               (= input-2 replace-1-y))
  (=> (= line-input-2 line-replace-1-z)               (= input-2 replace-1-z))
  (=> (= line-input-2 line-replace-1-output)          (= input-2 replace-1-output))

  (=> (= line-input-2 line-replace-2-x)               (= input-2 replace-2-x))
  (=> (= line-input-2 line-replace-2-y)               (= input-2 replace-2-y))
  (=> (= line-input-2 line-replace-2-z)               (= input-2 replace-2-z))
  (=> (= line-input-2 line-replace-2-output)          (= input-2 replace-2-output))

  (=> (= line-input-2 line-output)                    (= input-2 output))

  (=> (= line-input-3 line-replace-1-x)               (= input-3 replace-1-x))
  (=> (= line-input-3 line-replace-1-y)               (= input-3 replace-1-y))
  (=> (= line-input-3 line-replace-1-z)               (= input-3 replace-1-z))
  (=> (= line-input-3 line-replace-1-output)          (= input-3 replace-1-output))

  (=> (= line-input-3 line-replace-2-x)               (= input-3 replace-2-x))
  (=> (= line-input-3 line-replace-2-y)               (= input-3 replace-2-y))
  (=> (= line-input-3 line-replace-2-z)               (= input-3 replace-2-z))
  (=> (= line-input-3 line-replace-2-output)          (= input-3 replace-2-output))

  (=> (= line-input-3 line-output)                    (= input-3 output))

  (=> (= line-input-4 line-replace-1-x)               (= input-4 replace-1-x))
  (=> (= line-input-4 line-replace-1-y)               (= input-4 replace-1-y))
  (=> (= line-input-4 line-replace-1-z)               (= input-4 replace-1-z))
  (=> (= line-input-4 line-replace-1-output)          (= input-4 replace-1-output))

  (=> (= line-input-4 line-replace-2-x)               (= input-4 replace-2-x))
  (=> (= line-input-4 line-replace-2-y)               (= input-4 replace-2-y))
  (=> (= line-input-4 line-replace-2-z)               (= input-4 replace-2-z))
  (=> (= line-input-4 line-replace-2-output)          (= input-4 replace-2-output))

  (=> (= line-input-4 line-output)                    (= input-4 output))

  (=> (= line-input-5 line-replace-1-x)               (= input-5 replace-1-x))
  (=> (= line-input-5 line-replace-1-y)               (= input-5 replace-1-y))
  (=> (= line-input-5 line-replace-1-z)               (= input-5 replace-1-z))
  (=> (= line-input-5 line-replace-1-output)          (= input-5 replace-1-output))

  (=> (= line-input-5 line-replace-2-x)               (= input-5 replace-2-x))
  (=> (= line-input-5 line-replace-2-y)               (= input-5 replace-2-y))
  (=> (= line-input-5 line-replace-2-z)               (= input-5 replace-2-z))
  (=> (= line-input-5 line-replace-2-output)          (= input-5 replace-2-output))

  (=> (= line-input-5 line-output)                    (= input-5 output))

  (=> (= line-replace-1-x line-replace-1-y)           (= replace-1-x replace-1-y))
  (=> (= line-replace-1-x line-replace-1-z)           (= replace-1-x replace-1-z))
  (=> (= line-replace-1-y line-replace-1-z)           (= replace-1-y replace-1-z))

  (=> (= line-replace-2-x line-replace-2-y)           (= replace-2-x replace-2-y))
  (=> (= line-replace-2-x line-replace-2-z)           (= replace-2-x replace-2-z))
  (=> (= line-replace-2-y line-replace-2-z)           (= replace-2-y replace-2-z))

  (=> (= line-replace-1-x line-replace-2-x)           (= replace-1-x replace-2-x))
  (=> (= line-replace-1-x line-replace-2-y)           (= replace-1-x replace-2-y))
  (=> (= line-replace-1-x line-replace-2-z)           (= replace-1-x replace-2-z))

  (=> (= line-replace-1-y line-replace-2-x)           (= replace-1-y replace-2-x))
  (=> (= line-replace-1-y line-replace-2-y)           (= replace-1-y replace-2-y))
  (=> (= line-replace-1-y line-replace-2-z)           (= replace-1-y replace-2-z))

  (=> (= line-replace-1-z line-replace-2-x)           (= replace-1-z replace-2-x))
  (=> (= line-replace-1-z line-replace-2-y)           (= replace-1-z replace-2-y))
  (=> (= line-replace-1-z line-replace-2-z)           (= replace-1-z replace-2-z))

  (=> (= line-replace-1-x line-replace-1-output)      (= replace-1-x replace-1-output))
  (=> (= line-replace-1-x line-replace-2-output)      (= replace-1-x replace-2-output))
  (=> (= line-replace-1-x line-output)                (= replace-1-x output))

  (=> (= line-replace-1-y line-replace-1-output)      (= replace-1-y replace-1-output))
  (=> (= line-replace-1-y line-replace-2-output)      (= replace-1-y replace-2-output))
  (=> (= line-replace-1-y line-output)                (= replace-1-y output))

  (=> (= line-replace-1-z line-replace-1-output)      (= replace-1-z replace-1-output))
  (=> (= line-replace-1-z line-replace-2-output)      (= replace-1-z replace-2-output))
  (=> (= line-replace-1-z line-output)                (= replace-1-z output))

  (=> (= line-replace-1-output line-replace-2-output) (= replace-1-output replace-2-output))
  (=> (= line-replace-1-output line-output)           (= replace-1-output output))
  (=> (= line-replace-2-output line-output)           (= replace-2-output output))
))

;; Example

(assert (and (= input-1 "hslcy")
             (= input-2 "hslc")
             (= input-3 "dzoi")
             (= input-4 "dzoi")
             (= input-5 "pnhz")))
(assert (= output "pnhzy"))

(check-sat)
(get-model)
