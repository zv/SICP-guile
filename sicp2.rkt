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

