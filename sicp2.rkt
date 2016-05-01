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

#| Exercise: 2.28
|#
(define (fringe xs)
  (cond [(null? xs) null]
        [(list? xs) (append (fringe (first xs))
                            (fringe (rest xs)))]
        [else (list xs)]))


#| Exercise: 2.29
|#
;; Racket Style
(struct mobile (l r)
  #:transparent)
(struct mbranch (len structure)
  #:transparent)

(define (total-weight node)
  (let [(mstruct (mbranch-structure node))]
    (if (mobile? mstruct)
        (+ (total-weight (mobile-l node))
           (total-weight (mobile-r node)))
        mstruct)))

(define (balanced-mobile? mbl)
  (= (total-weight (mobile-l mbl))
     (total-weight (mobile-r mbl))))

;;; Guile Style
(define (make-mobile left right) '(left right))
(define (make-branch len structure) '(len structure))

(define (sip-total-weight node)
  (let [(mstruct (cadr node))]
    (if (number? mstruct) mstruct
        (+ (sip-total-weight (left-branch node))
           (sip-total-weight (right-branch node))))))

(define (sip-balanced-mobile? mbl)
  (= (total-weight (left-branch mbl))
     (total-weight (right-branch mbl))))

#| Exercise: 2.30
|#
(define (square-tree tree)
  (map (λ (node)
         (if (list? node) (square-tree node)
             (* node node))) tree))
#| Exercise: 2.31
|#
(define (tree-map fn tree)
  (map (λ (node)
         (if (list? node) (tree-map fn node)
             (fn node))) tree))

#| Exercise: 2.32
|#
(define (subsets s)
  (if (null? s) (list null)
      (let [(restl (subsets (cdr s)))]
        (append restl (map (λ (x) (cons (car s) x)) restl)))))

;; -- UTILITIES -------------------------------------
(define (filter predicate sequence)
  (cond ((null? sequence) null)
        ((predicate (car sequence))
         (cons (car sequence)
               (filter predicate (cdr sequence))))
        (else (filter predicate (cdr sequence)))))

(define (accumulate op initial sequence)
  (if (null? sequence)
      initial
      (op (car sequence)
          (accumulate op initial (cdr sequence)))))

(define (flatmap proc seq)
  (accumulate append null (map proc seq)))

(define (permutations s)
  (if (null? s)                    ; empty set?
      (list null)                   ; sequence containing empty set
      (flatmap (lambda (x)
                 (map (lambda (p) (cons x p))
                      (permutations (remove x s))))
               s)))
;; --------------------------------------------------
#| Exercise: 2.33
|#

(define (map-z p sequence)
  (accumulate (λ (x y) (cons (p x) y)) null sequence))

(define (append-z seq1 seq2)
  (accumulate cons seq2 seq1))

(define (length-z sequence)
  (accumulate (λ (x y) (+ y 1)) 0 sequence))


#| Exercise: 2.34
|#
(define (horner-eval x coefficient-sequence)
  (accumulate (λ (this-coeff higher-terms)
                (+ this-coeff (* x higher-terms)))
              0
              coefficient-sequence))


#| Exercise: 2.3
|#
(struct rectangle-s (height width)
  #:guard (λ (height width type-name)
            (if [and (segment? height) (segment? width)]
                (values height width)
                (error "not a valid rectangle"))))

(struct rectangle (a b)
  #:guard (λ (a b type-name)
            (if [and (coordinate? a) (coordinate? b)]
                (values a b)
                (error "not a valid rectangle"))))

(define (area rect)
  (* (rect-height rect) (rect-width rect)))

(define (rect-height rect)
  (abs (if (rectangle-s? rect)
           (- (coordinate-y (segment-start (rectangle-s-height rect)))
              (coordinate-y (segment-end   (rectangle-s-height rect))))
           (- (coordinate-y (rectangle-a rect))
              (coordinate-y (rectangle-b rect))))))

(define (rect-width rect)
  (abs (if (rectangle-s? rect)
           (- (coordinate-x (segment-start (rectangle-s-width rect)))
              (coordinate-x (segment-end   (rectangle-s-width rect))))
           (- (coordinate-x (rectangle-a rect))
              (coordinate-x (rectangle-b rect))))))

#| Exercise: 2.35
|#
(define (count-leaves-z t)
  (accumulate + 0 (map count-leaves t)))

#| Exercise: 2.36
|#
(define (accumulate-n op ini seqs)
  (if (null? (car seqs))
      null
      (cons (accumulate op ini (map (lambda (x) (car x)) seqs))
            (accumulate-n op ini (map (lambda (x) (cdr x)) seqs)))))

#| Exercise: 2.37
|#
(define zv-matrix '((1 2 3 4) (4 5 6 6) (6 7 8 9)))
(define zv-square '((1 2 3) (4 5 6) (6 7 8)))

(define (dot-product v w)
  (accumulate + 0 (map * v w)))

(define (matrix-*-vector m v)
  (map (lambda (row) (dot-product row v)) m))

(define (transpose mat)
  (accumulate-n cons '() mat))

(define (matrix-*-matrix m n)
   (let [(elems (transpose n))]
     (map (λ (row) (matrix-*-vector elems row)) m)))

#| Exercise: 2.38
|#
;;;; skipped

#| Exercise: 2.39
|#
(define (reverse-fr sequence)
  (foldr (lambda (x y) (append y `(,x))) null sequence))

(define (reverse-fl sequence)
  (foldl (lambda (x y) (cons x y)) null sequence))

