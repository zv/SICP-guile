#lang racket
(require (lib "trace.ss"))

(define (square x) (* x x))
(define (largest-sums x y z)
  (+
   (if (> x y) (square x) (square y))
   (if (> y z) (square y) (square z))))

(define (inc a) (+ a 1))
(define (dec a) (- a 1))

(define (plus a b)
  (if (= a 0)
      b
      (inc (plus (dec a) b))))

(define (plus1 a b)
  (if (= a 0)
      b
      (plus1 (dec a) (inc b))))

(define (Ackermann x y)
  (cond ((= y 0) 0)
        ((= x 0) (* 2 y))
        ((= y 1) 2)
        (else (Ackermann (- x 1)
                 (Ackermann x (- y 1))))))
