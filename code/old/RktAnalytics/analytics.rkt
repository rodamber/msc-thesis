#lang racket

(require json)

;; TODO: Check out 'operands' in the documentation (runtime properties, etc)

(define builtin-functions
  (set
   'BooleanToInteger          'BooleanToText             'DateTimeToDate
   'DateTimeToText            'DateTimeToTime            'DateToDateTime
   'DateToText                'DecimalToBoolean          'DecimalToInteger
   'DecimalToIntegerValidate  'DecimalToLongInteger      'DecimalToLongIntegerValidate
   'DecimalToText             'LongIntegerToInteger      'LongIntegerToIntegerValidate
   'LongIntegerToIdentifier   'LongIntegerToText         'IdentifierToInteger
   'IdentifierToLongInteger   'IdentifierToText          'IntegerToBoolean
   'IntegerToDecimal          'IntegerToIdentifier       'IntegerToText
   'NullDate                  'NullIdentifier            'NullObject
   'NullBinary                'NullTextIdentifier        'TextToDate
   'TextToDateTime            'TextToDateTimeValidate    'TextToDateValidate
   'TextToDecimal             'TextToDecimalValidate     'TextToIdentifier
   'TextToInteger             'TextToLongInteger         'TextToIntegerValidate
   'TextToLongIntegerValidate 'TextToTime                'TextToTimeValidate
   'TimeToText                'ToObject

   'AddDays                   'AddHours                  'AddMinutes
   'AddMonths                 'AddSeconds                'AddYears
   'BuildDateTime             'CurrDate                  'CurrDateTime
   'CurrTime                  'Day                       'DayOfWeek
   'DiffDays                  'DiffHours                 'DiffMinutes
   'DiffSeconds               'Hour                      'Minute
   'Month                     'NewDate                   'NewDateTime
   'NewTime                   'Second                    'Year

   'EmailAddressCreate        'EmailAddressesConcatenate 'EmailAddressValidate

   'GetApplicationServerType  'GetCurrentLocale          'GetDatabaseProvider
   'GetUserAgent              'GetOwnerEspaceIdentifier  'GetEntryEspaceName
   'GetEntryEspaceId          'GetObsoleteTenantId

   'FormatDecimal             'FormatPercent             'FormatPhoneNumber
   'FormatText                'FormatDateTime

   'Abs                       'Mod                       'Power
   'Round                     'Sqrt                      'Trunc

   'GeneratePassword          'If                        'IsLoadingScreen
   'CurrentThemeIsMobile

   'Max                       'Min                       'Sign

   'CheckRole                 'GetUserId

   'Chr                       'Concat                    'EncodeHtml
   'EncodeJavaScript          'EncodeSql                 'EncodeUrl
   'Index                     'Length                    'NewLine
   'Replace                   'Substr                    'ToLower
   'ToUpper                   'Trim                      'TrimEnd
   'TrimStart

   'AddPersonalAreaToURLPath  'GetBookmarkableURL        'GetPersonalAreaName
   'GetOwnerURLPath           'GetExceptionURL))

(define builtin-operators
  (set
   ; Numeric
   '+ '- '* '/

   ; Logical and Boolean
   'and 'or 'not '= '< '> '<> '<= '>=

   ; Equality operators
   '= '<>

   ; Like
   'Like

   ; Indexer (edge case: name of the symbol does not match the operator)
   'Ix))

(define builtin-types
  (set
   '|Binary Data|
   'Boolean
   'Currency
   'Date
   'Time
   '|Date Time|
   'Integer
   '|Long Integer|
   'Decimal
   'Email
   '|Phone Number|
   'Text
   'Identifier))

(define (identifier? x)
  (string-suffix? x "Identifier"))

(define (builtin-function? f)
  (set-member? builtin-functions (string->symbol f)))

(define (builtin-type? t)
  (set-member? builtin-types (string->symbol t)))

(define (expr-key  jsexpr) (hash-ref jsexpr 'exprKey))
(define (functions jsexpr) (hash-ref jsexpr 'functions))
(define (oml-key   jsexpr) (hash-ref jsexpr 'oml))
(define (refs      jsexpr) (hash-ref jsexpr 'refs))
(define (text      jsexpr) (hash-ref jsexpr 'text))
(define (type      jsexpr) (hash-ref jsexpr 'type))

(define all-exprs
  (lazy
   (with-input-from-file "data/exprs-3-6.jsonl"
     (lambda ()
       (for/list ([l (in-lines)])
         (string->jsexpr l))))))

(define all-exprs-types
  (lazy
   (for/set ([expr (force all-exprs)])
     (type expr))))

(define all-return-types-except-ids
  (lazy
   (for/set ([type (force all-exprs-types)]
             #:when (not (identifier? type)))
     type)))

(define (make-hist seq)
  (for*/fold ([h (hash)])
             ([x seq])
    (hash-update h
                 (string->symbol x)
                 add1
                 0)))

(define (top-n-hits hist n)
  (define sorted (sort (hash->list hist)
                       #:key cdr >))
  (take-at-most sorted n))
; where
(define (take-at-most lst n)
  (if (n . <= . (length lst))
      (take lst n)
      lst))

(define (% x y #:precision [precision 2])
  (if (zero? y)
      (~r 0.00         #:precision (quasiquote (= ,precision)))
      (~r (/ x y 0.01) #:precision (quasiquote (= ,precision)))))

(define (main-how-many #:lower-bound [lower-bound 0]
                       #:upper-bound [upper-bound 5]
                       #:examples? [examples? #f])
  (for ([i (in-range lower-bound (add1 upper-bound))])
    (define exprs
      (filter (λ (e) (i . <= . (length (functions e))))
              (force all-exprs)))
    (define exprs-builtin-functions
      (filter (λ (e) (andmap builtin-function? (functions e)))
              exprs))
    (define (example exprs)
      (define xs (filter (λ (e) (i . = .(length (functions e))))
                          exprs))
      (define len (length xs))
      (when (positive? len)
        (text (list-ref xs (random len)))))
    (define (show-example exprs)
      (if examples?
          (example exprs)
          "<omitted>"))
    (define len-exprs (length exprs))
    (define len-exprs-builtin-functions (length exprs-builtin-functions))

    (printf #<<str>>
There are ~a expressions that use ~a or more functions:
  + Example: ~a
  + ~a (~a%) use only _builtin_ functions.
    - Example: ~a~n
str>>
            len-exprs i
            (show-example exprs)
            len-exprs-builtin-functions
            (% len-exprs-builtin-functions len-exprs)
            (show-example exprs-builtin-functions))))

(define (main-top #:top-len [top-len 5])
  (define (top f)
    (define lst (f (force all-exprs)))
    (values
     (top-n-hits (make-hist lst) top-len)
     (length lst)))

  (define (print-top assoc total)
    (for ([pair assoc]
          [i (in-range 1 (add1 (length assoc)))])
      (match pair
        [(cons elem count)
         (printf "\t~a. ~a: ~a (~a%)~n"
                 i elem count
                 (~r (/ count total 0.01)
                     #:precision '(= 2)))])))

  (let-values ([(top-functions total)
                (top (λ (es) (append-map functions es)))])
    (printf "These are the top ~a most commonly used functions:~n" top-len)
    (print-top top-functions total))

  (let-values ([(top-builtin-functions total)
                (top (λ (es) (filter builtin-function?
                                     (append-map functions es))))])
    (printf "These are the top ~a most commonly used _builtin_ functions:~n" top-len)
    (print-top top-builtin-functions total))

  (let-values ([(top-types total)
                (top (λ (es) (map type es)))])
    (printf "These are the top ~a most common return types:~n" top-len)
    (print-top top-types total))

  (let-values ([(top-builtin-types total)
                (top (λ (es) (filter builtin-type? (map type es))))])
    (printf "These are the top ~a most common _builtin_ return types:~n" top-len)
    (print-top top-builtin-types total))
  )

(define (main #:lb [lb 0] #:ub [ub 14] #:exs? [exs? #f] #:tl [tl 10])
  (printf "There are ~a expressions in total.~n"
          (length (force all-exprs)))

  (main-how-many #:lower-bound lb
                 #:upper-bound ub
                 #:examples? exs?)

  (main-top #:top-len tl))

(define (write-results #:lb [lb 0] #:ub [ub 14] #:exs? [exs? #f] #:tl [tl 10])
  (define filename
    (if exs?
        "results-with-examples.txt"
        "results.txt"))
  (with-output-to-file filename
    (λ () (main lb ub exs? tl))
    #:exists 'replace))

;; -----------------------------------------------------------------------------

;; # Data Conversion
;; BooleanToInteger(​Boolean)
;; BooleanToText(​Boolean)
;; DateTimeToDate(​DateTime)
;; DateTimeToText(​DateTime)
;; DateTimeToTime(​DateTime)
;; DateToDateTime(​Date)
;; DateToText(​Date)
;; DecimalToBoolean(​Decimal)
;; DecimalToInteger(​Decimal)
;; DecimalToIntegerValidate(​Decimal)
;; DecimalToLongInteger(​Decimal)
;; DecimalToLongIntegerValidate(​Decimal)
;; DecimalToText(​Decimal)
;; LongIntegerToInteger(​LongInteger)
;; LongIntegerToIntegerValidate(​LongInteger)
;; LongIntegerToIdentifier(​LongInteger)
;; LongIntegerToText(​LongInteger)
;; IdentifierToInteger(​EntityReference)
;; IdentifierToLongInteger(​EntityReferenceLongInteger)
;; IdentifierToText(​EntityReferenceText)
;; IntegerToBoolean(​Integer)
;; IntegerToDecimal(​Integer)
;; IntegerToIdentifier(​Integer)
;; IntegerToText(​Integer)
;; NullDate()
;; NullIdentifier()
;; NullObject()
;; NullBinary()
;; NullTextIdentifier()
;; TextToDate(​Text)
;; TextToDateTime(​Text)
;; TextToDateTimeValidate(​Text)
;; TextToDateValidate(​Text)
;; TextToDecimal(​Text)
;; TextToDecimalValidate(​Text)
;; TextToIdentifier(​Text)
;; TextToInteger(​Text)
;; TextToLongInteger(​Text)
;; TextToIntegerValidate(​Text)
;; TextToLongIntegerValidate(​Text)
;; TextToTime(​Text)
;; TextToTimeValidate(​Text)
;; TimeToText(​Time)
;; ToObject(​Generic)
;;
;; # Data and Time
;; AddDays(​DateTime, Integer)
;; AddHours(​DateTime, Integer)
;; AddMinutes(​DateTime, Integer)
;; AddMonths(​DateTime, Integer)
;; AddSeconds(​DateTime, Integer)
;; AddYears(​DateTime, Integer)
;; BuildDateTime(​Date, Time)
;; CurrDate()
;; CurrDateTime()
;; CurrTime()
;; Day(​DateTime)
;; DayOfWeek(​DateTime)
;; DiffDays(​DateTime, DateTime)
;; DiffHours(​DateTime, DateTime)
;; DiffMinutes(​DateTime, DateTime)
;; DiffSeconds(​DateTime, DateTime)
;; Hour(​DateTime)
;; Minute(​DateTime)
;; Month(​DateTime)
;; NewDate(​Integer, Integer, Integer)
;; NewDateTime(​Integer, Integer, Integer, Integer, Integer, Integer)
;; NewTime(​Integer, Integer, Integer)
;; Second(​DateTime)
;; Year(​DateTime)
;;
;; # Email
;; EmailAddressCreate(​Text, Text)
;; EmailAddressesConcatenate(​Text, Text)
;; EmailAddressValidate(​Text)
;;
;; # Environment
;; GetApplicationServerType()
;; GetCurrentLocale()
;; GetDatabaseProvider()
;; GetUserAgent()
;; GetOwnerEspaceIdentifier()
;; GetEntryEspaceName()
;; GetEntryEspaceId()
;; GetObsoleteTenantId()
;;
;; # Format
;; FormatCurrency(​Currency, Text, Integer, Text, Text)
;; FormatDecimal(​Decimal, Integer, Text, Text)
;; FormatPercent(​Decimal, Integer, Text)
;; FormatPhoneNumber(​Text, Integer, Integer, Integer, Text, Text, Text)
;; FormatText(​Text, Integer, Integer, Boolean, Text)
;; FormatDateTime(​DateTime, Text)
;;
;; # Math
;; Abs(​Decimal)
;; Mod(​Decimal, Decimal)
;; Power(​Decimal, Decimal)
;; Round(​Decimal, Integer)
;; Sqrt(​Decimal)
;; Trunc(​Decimal)
;;
;; # Misc
;; GeneratePassword(​Integer, Boolean)
;; If(​Boolean, Generic, Generic)
;; IsLoadingScreen()
;; CurrentThemeIsMobile()
;;
;; # Numeric
;; Max(​Decimal, Decimal)
;; Min(​Decimal, Decimal)
;; Sign(​Decimal)
;;
;; # Role
;; CheckRole(​RoleId, UserId)
;; GetUserId()
;;
;; # Text
;; Chr(​Integer)
;; Concat(​Text, Text)
;; EncodeHtml(​Text)
;; EncodeJavaScript(​Text)
;; EncodeSql(​Text)
;; EncodeUrl(​Text)
;; Index(​Text, Text, Integer, Boolean, Boolean)
;; Length(​Text)
;; NewLine()
;; Replace(​Text, Text, Text)
;; Substr(​Text, Integer, Integer)
;; ToLower(​Text)
;; ToUpper(​Text)
;; Trim(​Text)
;; TrimEnd(​Text)
;; TrimStart(​Text)
;;
;; # URL
;; AddPersonalAreaToURLPath(​Text)
;; GetBookmarkableURL()
;; GetPersonalAreaName()
;; GetOwnerURLPath()
;; GetExceptionURL()
