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

#| Exercise: 2.40
|#
(define (unique-pairs n)
  (flatmap (λ (i)
             (map (λ (j) (list i j))
                  (range i n)))
           (range 1 n)))

(define (prime? n)
  (empty?
   (filter (lambda (p) (= n (* (car p) (cadr p))))
           (unique-pairs n))))

(define (prime-sum? pair) (prime? (+ (car pair) (cadr pair))))

(define (make-pair-sum pair)
  (list (car pair) (cadr pair) (+ (car pair) (cadr pair))))

(define (prime-sum-pairs n)
  (map make-pair-sum (filter prime-sum? (unique-pairs n))))

#| Exercise: 2.41
|#
(define (triplets-summing-to s n)
  (define (unique-triplets n)
    (flatmap (λ (i)
               (flatmap (λ (j)
                          (map (λ (k)
                                 (list i j k))
                               (range j n)))
                        (range i n)))
             (range 0 n)))

  (filter (λ (t) (= s (foldr + 0 t)))
          (unique-triplets n)))

#| Exercise: 2.42
|# (finally!)
;;; Real Solution (copied)
(define (queens board-size)
  (define (queen-cols k)
    (if (= k 0)
        (list empty-board)
        (filter
         (lambda (positions) (safe? k positions))
         (flatmap
          (lambda (rest-of-queens)
            (map (lambda (new-row)
                   (adjoin-position new-row k rest-of-queens))
                 (range 1 board-size)))
          (queen-cols (- k 1))))))
  (queen-cols board-size))

;; (struct posn (row col)
;;   #:transparent)

;; (define (make-position row col) (cons row col))

;; (define empty-board null)

;; (define (adjoin-position row col positions)
;;   (append positions (list (posn row col))))

;; (define (safe? col positions)
;;   (let ((kth-queen (list-ref positions (- col 1)))
;;         (other-queens (filter (λ (q)
;;                                 (not (= col (posn-col q))))
;;                               positions)))
;;     (define (attacks? q1 q2)
;;       ;; what the fuck???
;;       (or (= (posn-row q1) (posn-row q2))
;;           (= (abs (- (posn-row q1) (posn-row q2)))
;;              (abs (- (posn-col q1) (posn-col q2))))))

;;     (define (iter q board)
;;       (or (null? board)
;;           (and (not (attacks? q (car board)))
;;                (iter q (cdr board)))))
;;     (iter kth-queen other-queens)))


(define empty-board null)

(define (adjoin-position row positions)
  (cons row positions))

(define (safe? position)

  (define board-size (length position))

  (define (safe-diagonal? position)

    ; test the position for the newly placed queen
    (define (col-safe? new-row col position)
      (cond ((> col board-size) true)
            ((= (abs (- new-row (car position)))
                ; the new qeeen's position is always on column 1
                (abs (- col 1))) false)
            (else (col-safe? new-row (+ col 1) (cdr position)))))

    ; the new queen's position is always in column 1
    ; so the initial column to check is always 2
    (col-safe? (car position) 2 (cdr position)))

  (define (safe-horizontal? position)
    ; does the new row (car) appear anywhere else?
    (not (member (car position) (cdr position))))

  (or (= (length position) 1)  ; 1x1 board
      (and (safe-horizontal? position)
           (safe-diagonal?   position))))

;; ------------------------------------------------------------
;; Picture Exercises are included in `picture.rkt'
;; ------------------------------------------------------------

;;;; Symbolic Manipulation

#| Exercise: 2.53
|#

;;; (list 'a 'b 'c)                         => '(a b c)
;;; (list (list 'george))                   => '((georger))
;;; (cdr '((x1 x2) (y1 y2)))                => '(y1 y2)
;;; (cadr '((x1 x2) (y1 y2)))               => '(y1 y2)
;;; (pair? (car '(a short list)))           => 'a
;;; (memq 'red '((red shoes) (blue socks))) => null
;;; (memq 'red '(red shoes blue socks))     => '(shoes blue socks)

#| Exercise: 2.54
|#
(define (zv-equal? a b)
  (cond [(or (empty? a) (empty? b)) (eq? a b)]
        [(and (list? a) (list? b))
         (and (eq? (car a) (car b))
              (zv-equal? (cdr a) (cdr b)))]
        [(or (list? a) (list? b)) false]
        [else (eq? a b)]))

#| Exercise: 2.4
|#
;;; whoa!!!
(define (recons x y)
  (λ (m) (m x y)))

(define (recar z)
  (z (λ (p q) p)))

(define (recdr z)
  (z (λ (p q) q)))


#| Exercise: 2.55
|#
;; It is a "double quoted" item, e.g the symbols (quote abracadabra) resolve to
;; the *function* quote, which is created from syntax sugar.


;; Utilities
(define (deriv expr var)
  (cond [(number? expr) 0]
        [(variable? expr)
         (if (same-variable? expr var) 1 0)]
        [(sum? expr)
         (make-sum (deriv (addend expr) var)
                   (deriv (augend expr) var))]
        [(product? expr)
         (make-sum
          (make-product
           (multiplier expr)
           (deriv (multiplicand expr) var))
          (make-product
           (deriv (multiplier expr) var)
           (multiplicand expr)))]
        [(exponentiation? expr)
         (make-product
          (make-product
           (exponent expr)
           (make-exponent (base expr)
                          (- (exponent expr) 1)))
          (deriv (base expr) var))]
        [else (error "unknown exprression type: DERIV" expr)]))

(define (variable? x) (symbol? x))

(define (same-variable? v1 v2)
  (and (variable? v1)
       (variable? v2)
       (eq? v1 v2)))

(define (=number? exp num)
  (and (number? exp) (= exp num)))
;; A sum is a list whose first element is the symbol +:
;; TODO
(define (sum? x)
  (and (list? x) (eq? (car x) '+)))

(define (product? x)
  (and (list? x) (eq? (car x) '*)))


#| Exercise: 2.56
|#
(define (exponentiation? x)
  (and (list? x) (eq? (car x) 'expt)))
(define (base p) (cadr p))
(define (exponent p) (caddr p))

(define (make-exponent e1 e2)
  (cond [(=number? e1 0) 1]
        [(=number? e2 0) 1]
        [(and (number? e1) (number? e2)
              (expt e1 e2))]
        [else `(expt ,e1 ,e2)]))

#| Exercise: 2.57
|#
(define (make-sum a1 a2)
  (cond [(=number? a1 0) a2]
        [(=number? a2 0) a1]
        [(and (number? a1) (number? a2)
              (+ a1 a2))]
        [else `(+ ,a1 ,a2)]))

(define (make-product m1 m2)
  (cond [(or (=number? m1 0)
             (=number? m2 0))
         0]
        [(=number? m1 1) m2]
        [(=number? m2 1) m1]
        [(and (number? m1) (number? m2))
         (* m1 m2)]
        [else (list '* m1 m2)]))

(define (addend s) (cadr s))
(define (augend s)
  (if (null? (cdddr s))
      (caddr s)
      `(+ ,@(cddr s))))
(define (multiplier s) (cadr s))
(define (multiplicand s)
  (if (null? (cdddr s))
      (caddr s)
      `(* ,@(cddr s))))

#| Exercise: 2.58
|#
;;; 1.
(define (infix-addend s) (car s))
(define (infix-augend s) (caddr s))
(define (infix-multiplier s) (car s))
(define (infix-multiplicand s) (caddr s))

(define (infix-sum? x)
  (and (list? x) (eq? (cadr x) '+)))

(define (infix-product? x)
  (and (list? x) (eq? (cadr x) '*)))

(define (infix-make-sum a1 a2)
  (cond [(=number? a1 0) a2]
        [(=number? a2 0) a1]
        [(and (number? a1) (number? a2)
              (+ a1 a2))]
        [else `(,a1 + ,a2)]))

(define (infix-make-product m1 m2)
  (cond [(or (=number? m1 0)
             (=number? m2 0)) 0]
        [(=number? m1 1) m2]
        [(=number? m2 1) m1]
        [(and (number? m1) (number? m2))
         (* m1 m2)]
        [else `(,m1 * ,m2)]))

(define (infix-deriv expr var)
  "This function is for computing the derivative of a simple, infix'd function"
  (cond [(number? expr) 0]
        [(variable? expr)
         (if (same-variable? expr var) 1 0)]
        [(infix-sum? expr)
         (infix-make-sum (infix-deriv (infix-addend expr) var)
                         (infix-deriv (infix-augend expr) var))]
        [(infix-product? expr)
         (infix-make-sum
          (infix-make-product
           (infix-multiplier expr)
           (infix-deriv (infix-multiplicand expr) var))
          (infix-make-product
           (infix-deriv (infix-multiplier expr) var)
           (infix-multiplicand expr)))]
        [else (error "unknown exprression type: DERIV" expr)]))
;;; 2.
#|
(x + 3 * (x + y + 2))
(+ x (* 3 (+ x y 2)))
4x + 3y + 6
x+3 * x
x^2 + 9
|#


;; Set Utils
(define (element-of-set? elt ss)
  (cond [(empty? ss) false]
        [(equal? elt (car ss)) true]
        [else (element-of-set? elt (cdr ss))]))

(define (adjoin-set elt ss)
  (if (element-of-set? elt ss)
      set
      (cons elt ss)))

(define (intersection ss1 ss2)
  (cond [(or (empty? ss1) (empty? ss2)) null]
        [(element-of-set? (car ss1) ss2)
         (cons (car ss1)
               (intersection (cdr ss1) ss2))]
        [else (intersection (cdr ss1) ss2)]))

#| Exercise: 2.59
|#
(define (union-set ss1 ss2)
  (cond [(or (empty? ss1) (empty? ss2)) (append ss1 ss2)]
        [(element-of-set? (car ss1) ss2)
         (union-set (cdr ss1) ss2)]
        [else
         (cons (car ss1) (union-set (cdr ss1) ss2))]))

#| Exercise: 2.60
|#
(define (element-of-joined-set? elt ss)
  (element-of-set? elt ss))

(define (adjoin-joined-set elt ss)
  (cons elt ss))

(define (adjoin-intersection ss1 ss2)
  (intersection ss1 ss2))

(define (adjoin-union-set ss1 ss2)
  (append ss1 ss2))

;; Much cheaper, but to be useful it would require another deduplication pass.
(define (element-of-set-ordered? elt ss)
  (cond [(empty? ss) false]
        [(= elt (car ss)) true]
        [(< elt (car ss)) false]
        [else (element-of-set-ordered? elt (cdr ss))]))

(define (intersection-ordered-set set1 set2)
  "Begin by comparing the initial elements, x1 and x2, of the two sets. If x1
equals x2, then that gives an element of the intersection, and the rest of the
intersection is the intersection of the cdr-s of the two sets. Suppose, however,
that x1 is less than x2. Since x2 is the smallest element in set2, we can
immediately conclude that x1 cannot appear anywhere in set2 and hence is not in
the intersection. Hence, the intersection is equal to the intersection of set2
with the cdr of set1. Similarly, if x2 is less than x1, then the intersection is
given by the intersection of set1 with the cdr of set2. Here is the procedure"
  (if (or (null? set1) (null? set2)) null
      (let [(x1 (car set1)) (x2 (car set2))]
        (cond [(= x1 x2)
               (cons x1 (intersection-ordered-set (cdr set1) (cdr set2)))]
              [(< x1 x2)
               (intersection-ordered-set (cdr set1) set2)]
              [(> x1 x2)
               (intersection-ordered-set set1 (cdr set2))]))))

