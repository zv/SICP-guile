#lang racket
(require (lib "trace.ss"))

(define (inc a) (+ a 1))
(define (print-rat x)
  (display (numer x))
  (display '/)
  (display (denom x))
  (newline))


(define (numer x) (car x))

(define (denom x) (cdr x))

(define (add-rat x y)
  (make-rat (+ (* (numer x) (denom y))
               (* (numer y) (denom x)))
            (* (denom x) (denom y))))

(define (sub-rat x y)
  (make-rat (- (* (numer x) (denom y))
               (* (numer y) (denom x)))
            (* (denom x) (denom y))))

(define (mul-rat x y)
  (make-rat (* (numer x) (numer y))
            (* (denom x) (denom y))))

(define (div-rat x y)
  (make-rat (* (numer x) (denom y))
            (* (denom x) (numer y))))

(define (equal-rat? x y)
  (= (* (numer x) (denom y))
     (* (numer y) (denom x))))

(define (gcd a b)
  (if (= b 0) a
      (gcd b (remainder a b))))


#| Exercise: 2.1
|#
(define (make-rat n d)
  (let* [(g (abs (gcd n d)))
         (nsign (xor (negative? d)
                    (negative? n)))
         (num (/ (abs n) g))
         (den (/ (abs d) g))]
    (if nsign (cons (* -1 num) den)
        (cons num den))))

#| Exercise: 2.10
|#
(define (div-interval x y)
  (cond ((or (= 0 (upper-bound y)) (= 0 (lower-bound y)))
         (error "attempted to divide by the zero"))
        (else (mul-interval x
                            (make-interval (/ 1.0 (upper-bound y))
                                           (/ 1.0 (lower-bound y)))))))

#| Exercise: 2.11
|#
 (define (mul-interval x y)
  (let ((p1 (* (lower-bound x) (lower-bound y)))
        (p2 (* (lower-bound x) (upper-bound y)))
        (p3 (* (upper-bound x) (lower-bound y)))
        (p4 (* (upper-bound x) (upper-bound y))))
    (make-interval (min p1 p2 p3 p4)
                   (max p1 p2 p3 p4))))

#| Exercise: 2.17
|#
(define (last-pair lst)
  (let [(lastls (cdr lst))]
    (if (null? lastls) (car lst)
        (last-pair lastls))))

#| Exercise: 2.18
|#
(define (reverse-l lst)
  (if (null? lst) null
      (append (reverse-l (cdr lst)) (list (car lst)))))

(define (reverse-ls xs [result null])
  (cond [(null? xs) result]
        [else (reverse-ls (cdr xs) (cons (car xs) result))]))

#| Exercise: 2.19
|#
(define (valid-change n types)
  (filter (lambda (x) (<= x n)) types))

(define (zv-count-change amt types)
  (cond ((= amt 0) 1)
        ((or (< amt 0) (empty? (valid-change amt types))) 0)
        (else (foldr (lambda (x res) (+ res (zv-count-change (- amt x))))
                     0
                     (valid-change amt types)))))

#| Exercise: 2.20
|#

(define (same-parity elt . xs)
  (define (test-parity n) (= (remainder elt 2) (remainder n 2)))
  (filter test-parity xs))


#| Exercise: 2.21
|#
(define (square n) (* n n))

(define (square-list items)
  (if (null? items) null
      (cons (square (car items)) (square-list (cdr items)))))

(define (square-list-x items)
  (map square items))

#| Exercise: 2.22
|#
;;; Louis Reasoner has mixed up the arguments `answer' and `(square (car things))'
;;; In his second attempt
;; correct version of iterative
;; (define (square-list-b things [answer null])
;;     (if (null? things) answer
;;         (square-list-b (cdr things)
;;                        (append answer (list (square (car things)))))))

#| Exercise: 2.23
|#

(define (for-each-zv fn xs)
  (if [empty? xs] null
      (cons (fn (car xs))
            (for-each-zv fn (cdr xs))))
  #t)


;; not a exercize
(define (closest a b x)
  (if (< (abs (- x (/ (numer a) (denom a))))
         (abs (- x (/ (numer b) (denom b))))) a
      b))

(define (find-closest-rational x limit)
  (define (search-rationals n d top)
    (cond [(> n limit) (search-rationals 0 (inc d) top)]
          [(> d limit) top]
          [else
           (search-rationals (inc n)
                             d
                             (closest (make-rat n d) top x))]))
  (search-rationals 1 1 (make-rat 1 1)))

(define (find-closest-rational-t x limit)
  (define (search-rationals n d)
    (if (or (> n limit) (> d limit)) (make-rat n d)
        (closest (make-rat n d)
                 (closest
                  (search-rationals (inc n) d)
                  (search-rationals n (inc d))
                  x) x)))
  (search-rationals 1 1))

(define (count-leaves x)
  (cond ((null? x) 0)
        ((not (pair? x)) 1)
        (else (+ (count-leaves (car x))
                 (count-leaves (cdr x))))))

#| Exercise: 2.24
|#

#| Exercise: 2.2
|#
;;; racket
(struct coordinate (x y)
  #:transparent)
(struct segment (start end)
  #:transparent)


(define (midpoint segment)
  (let [(mid-x (/ (+ (coordinate-x (segment-start segment))
                  (coordinate-x (segment-end segment))) 2))
        (mid-y (/ (+ (coordinate-y (segment-start segment))
                     (coordinate-y (segment-end segment))) 2))]
    (coordinate mid-x mid-y)))

;; alternative scheme
(define (make-point x y) `(,x . ,y))
(define (make-segment s e) `(,s . ,e))
(define (x-point p) (car p))
(define (y-point p) (cdr p))
(define (start-segment segment) (car segment))
(define (end-segment segment) (cdr segment))

(define (print-point p)
  (display "(")
  (display (x-point p))
  (display ",")
  (display (y-point p))
  (display ")")
  (newline))

(define (midpoint-s segment)
  (make-segment
   (/ (+ (x-point (start-segment segment))
         (x-point (end-segment segment)))
      2)
   (/ (+ (y-point (start-segment segment))
         (y-point (end-segment segment)))
      2)))

#| Exercise: 2.25
|#
(define (is-sevens)
  [ printf "~a\n" (car (cdaddr '(1 3 (5 7) 9)))]
  [ printf "~a\n" (caar '((7)))]
  [ printf "~a\n" (cadadr (cadadr (cadadr '(1 (2 (3 (4 (5 (6 7)))))))))])

#| Exercise: 2.26
|#
(define two-twentysix-x (list 1 2 3))
(define two-twentysix-y (list 4 5 6))
;;; (append two-twentysix-x two-twentysix-y) => '(1 2 3 4 5 6)
;;; (cons two-twentysix-x two-twentysix-y)   => '((1 2 3) 4 5 6)
;;;  (list two-twentysix-x two-twentysix-y)  => '((1 2 3) (4 5 6))

#| Exercise: 2.27
|#
(define (deep-reverse-l lst)
  (cond [(null? lst) null]
        [(list? lst) (append
                      (deep-reverse-l (rest lst))
                      (list (deep-reverse-l (first lst))))]
        [else lst]))

