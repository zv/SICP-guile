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

(define (count-changex cnt)
  (define change '(1 5 10 25 50))
  (define valid-change
    (filter (lambda (x) (<= x cnt)) change))
  (if (= cnt 0) null
      (map (lambda (x) (cons x (count-changex (- cnt x))))
           valid-change)))
;; MY MAN!
(define (count-number-of-chng cnt)
  (define change '(1 5 10 25 50))
  (define valid-change
    (filter (lambda (x) (<= x cnt)) change))
  (if (= cnt 0) 1
      (map (lambda (x) (count-number-of-chng (- cnt x)))
           valid-change)))

(define (count-change amount)
  (cc amount 5))

(define (cc amount kinds-of-coins)
  (cond ((= amount 0) 1)
        ((or (< amount 0) (= kinds-of-coins 0)) 0)
        (else (+ (cc amount (- kinds-of-coins 1))
                 (cc (- amount (first-denomination kinds-of-coins)) kinds-of-coins)))))

(define (first-denomination kinds-of-coins)
  (cond ((= kinds-of-coins 1) 1)
        ((= kinds-of-coins 2) 5)
        ((= kinds-of-coins 3) 10)
        ((= kinds-of-coins 4) 25)
        ((= kinds-of-coins 5) 50)))

(define (valid-change n)
  (filter (lambda (x) (<= x n)) '(1 5 10 25 50)))

(define (zv-count-change amt)
  (cond ((= amt 0) 1)
        ((or (< amt 0) (empty? (valid-change amt))) 0)
        (else (foldr (lambda (x res) (+ res (zv-count-change (- amt x))))
                     0
                     (valid-change amt)))))

(define (pascals-triangle max-depth)
  (for ([i (in-range 1 max-depth)])
    (printf "~a~a\n" (make-string (- max-depth i) #\ ) (generate-row i))))

(define (generate-row depth)
  (for/list ([i (in-range 1 (+ 1 depth))])
    (generate-elt depth i)))

(define (generate-elt row col)
  (cond ([> 0 col] 0)
        ([> col (+ 1 row)] 0)
        ([> 0 row] 0)
        ([and (= row 1) (= col 1)] 1)
        (else (+ (generate-elt (- row 1) (- col 1))
                 (generate-elt (- row 1) col)))))

