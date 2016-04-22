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

