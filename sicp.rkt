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

(define (gcd a b)
  (if (= b 0)
      a
      (gcd b (remainder a b))))

(define (divides? a b) (= (modulo a b) 0))

(define (find-primes below)
  (primes-below (sequence->list (in-range 2 below))))

(define (primes-below unprimes)
  (if (empty? unprimes) '()
      (let ([curr (car unprimes)])
        (cons curr (primes-below
                    (filter-not (lambda (x) (divides? x curr)) unprimes))))))

(define (expmod base exp m)
  (cond ((= exp 0) 1)
        ((even? exp)
         (remainder (square (expmod base (/ exp 2) m))
                    m))
        (else
         (remainder (* base (expmod base (- exp 1) m))
                    m))))

(define (fermat-test n)
  (define (try-it a)
    (= (expmod a n n) a))
  (try-it (+ 1 (random (- n 1)))))

(define (deep-pp lst depth)
  (printf "\n~a(" (make-string depth #\ ))
  (map (lambda (elt) (cond
                       [(list? elt) (deep-pp elt (+ 1 depth))]
                       [else
                        (printf "\n")
                        (printf "~a~a" (make-string (+ 1 depth) #\ ) elt)
                        ]))
       lst)
  (printf ")"))


(define (deep-ppr lst depth)
  (let ((elt (car lst)))
    (if (list? elt)
        (begin
          (printf "~a(~a\n" (make-string depth #\ ) (car elt))
          (deep-ppr (cdr elt) (+ 1 depth)))
        ;; not a list
        (begin
          (printf "~a~a" (make-string depth #\ ) elt)))
    (if (empty? (cdr lst)) (printf ")")
        (begin
          (printf "\n")
          (deep-ppr (cdr lst) depth)))))

(define (summation term a next b)
  (if (> a b) 0
      (+ (term a)
         (summation term (next a) next b))))

(define (pi-approx a b)
  (define (pi-term a)
    (/ 1.0 (* a (+ a 2))))
  (define (pi-next b)
    (+ b 4))
  (summation pi-term a pi-next b))

(define (integral f a b dx)
  (define (add-dx x) (+ x dx))
  (* (summation f (+ a (/ dx 2.0)) add-dx b)
     dx))

#| Exercise: 1.29
|#
(define (cube a) (* a (* a a)))
(define (simpsons-stepper a b n) ((- b a) . / . n))
(define (simpsons-approx f a b n)
  (define (simpsons-term k)
    (define stepper (simpsons-stepper a b n))
    (let ([y (f (+ a (* k stepper)))])
      (cond [(or (= k n)
                 (zero? k)) y]
            [(even? k) (* 2 y)]
            [else (* 4 y)])))
  (* (/ (simpsons-stepper a b n) 3)
     (summation simpsons-term 0 inc n)))

#| Exercise: 1.30
|#
(define (sum term a next b)
  (define (iter a result)
    (if (> a b) result
        (iter (next a) (+ (term a) result))))
  (iter a 0))

#| Exercise: 1.31
|#
(define (product term a next b)
  (if (> a b) 1
      (* (term a)
         (product term (next a) next b))))

(define (zv-factorial n)
  (cond ((zero? n) 1)
        (else (product identity 1 inc n))))


(define (zv-pi-approx factor)
  (define (pi-term k)
    (let* ((numer1 (* 2 k))
           (denom (+ numer1 1))
           (numer2 (+ denom 1)))
      (printf "numer1: ~a @ denom ~a @ numer2 ~a\n" numer1 denom numer2)
      (/ (* numer1 numer2) (square denom))))
  (* 4.0 (product pi-term 1 inc factor)))

#| Exercise: 1.32
|#
(define (accumulate combiner null-value term a next b)
  (if (null-value a b) a
      (combiner (term a)
                (accumulate combiner null-value term (next a) next b))))

(define (average a b) (/ (+ a b) 2))
(define (close-enough? x y)
  (< (abs (- x y)) 0.001))

(define (search f neg-point pos-point)
  (let [(midpoint (average neg-point pos-point))]
    (if (close-enough? neg-point pos-point)
        midpoint
        (let [(test-value (f midpoint))]
          (cond ((positive? test-value)
                 (search f neg-point midpoint))
                ((negative? test-value)
                 (search f midpoint pos-point))
                (else midpoint))))))

(define (half-interval-method f a b)
  (let ((a-value (f a))
        (b-value (f b)))
    (cond ((and (negative? a-value) (positive? b-value))
           (search f a b))
          ((and (negative? b-value) (positive? a-value))
           (search f b a))
          (else
           (error "Values are not of opposite sign" a b)))))

(define tolerance 0.0001)
(define (fixed-point f first-guess)
  (define (close-enough? v1 v2)
    (< (abs (- v1 v2)) tolerance))
  (define (try guess)
    (let [(next (f guess))]
      (if (close-enough? guess next) next
          (try next))))
  (try first-guess))



#| Exercise: 1.35
|#
;; x = 1 + 1/x
;; x^2 = x + 1
;; x^2 - 1 = x
;; x^2 - x - 1 = 0
;; roots of quadratic equation: (-b +/ -√ (b^2 - 4ac)) / 2a
;; a = 1, b = -1, c = -1
;; = [ -b+√(b2-4ac) ] / 2a
;; = [ 1+√(1 + 4) ] / 2
;; = (1+√5) / 2

(define (compute-phi) (fixed-point (lambda (x) (+ 1 (/ 1 x))) 1.0))

#| Exercise: 1.36
|#
(define (fixed-point-p f first-guess tolerance)
  (define (guess a)
    (let [(next (f a))]
      (printf "~a\n" next)
      (if (< (abs (- a next)) tolerance) a
        (guess next))))
  (guess first-guess))

