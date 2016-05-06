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

#| Exercise: 2.61
|#
(define (adjoin-ordered-set elt os)
  "Takes advantage of the ordering of the set to stop when elt > (car os)"
  (if (empty? os) (list elt)
      (let [(oelt (car os))]
        (cond [(< elt oelt) (cons elt os)]
              [(> elt oelt)
               (cons oelt (adjoin-ordered-set elt (cdr os)))]
              [(= elt oelt) os]))))

#| Exercise: 2.62
|#
(define (union-ordered-set ss1 ss2)
  "Perform an O(n) union of 2 ordered sets"
  (if (or (empty? ss1) (empty? ss2)) (append ss1 ss2)
      (let [(x1 (car ss1))
            (x2 (car ss2))]
        (cond [(= x1 x2)
               (cons x1 (union-ordered-set (cdr ss1) (cdr ss2)))]
              [(< x1 x2)
               (cons x1 (union-ordered-set (cdr ss1) ss2) )]
              [(> x1 x2)
               (cons x2 (union-ordered-set ss1 (cdr ss2)) )]))))


#| Exercise: 2.63
|#

(define (sum-of-halves n)
  "Get the limit of a half a number, plus half of that, and so on"
  (if (= 0 n) 0
      (+ n (sum-of-halves (quotient n 2)))))

(define (get-depth tree)
  (if (null? tree) 0
      (+ 1 (max (get-depth (node-right tree))
           (get-depth (node-left tree))) )))

(struct node (val left right)
  #:transparent
  ;; #:methods gen:custom-write
  ;; [(define (write-proc self port mode)
  ;;    (fprintf port "(val: ~a left: ~a right: ~a)"
  ;;             (node-val self)
  ;;             (node-left self)
  ;;             (node-right self)))]
  )

(define (element-of-bset? elt ss)
  (cond [(null? ss) null]
        [(= elt (node-val ss)) true]
        [(< elt (node-val ss))
         (element-of-bset? elt (node-left ss))]
        [(> elt (node-val ss))
         (element-of-bset? elt (node-right ss))]))

(define (adjoin-bset elt ss)
  (cond [(null? ss) (node elt null null)]
        [(= elt (node-val ss)) ss]
        [(< elt (node-val ss))
         (node (node-val ss)
               (adjoin-bset elt (node-left ss))
               (node-right ss))]
        [(> elt (node-val ss))
         (node (node-val ss)
               (node-left ss)
               (adjoin-bset elt (node-right ss)))]))

(define (make-random-bset maxct [ct 0])
  "Helper function to create a binary treeset"
  (if (< maxct ct) (adjoin-bset (random maxct) null)
      (adjoin-bset (random maxct)
                   (make-random-bset maxct (inc ct)))))

(define (make-linear-bset maxct [ct 0])
  "Helper function to create a binary treeset"
  (if (< maxct ct) (adjoin-bset ct null)
      (adjoin-bset ct
                   (make-linear-bset maxct (inc ct)))))


#| Exercise: 2.63
|#
#|
1. I don't think they differ.
2. The former grows faster than the latter because of the `append' call. The orders of growth are identical.
|#
(define (tree->list-1 tree)
  (if (null? tree)
      '()
      (append
       (tree->list-1
        (node-left tree))
       (cons (node-val tree)
             (tree->list-1
              (node-right tree))))))

(define (tree->list-2 tree)
  (define (copy-to-list tree result-list)
    (if (null? tree)
        result-list
        (copy-to-list
         (node-left tree)
         (cons (node-val tree)
               (copy-to-list
                (node-right tree)
                result-list)))))
  (copy-to-list tree '()))

#| 2.64

Write a short paragraph explaining as clearly as you can how partial-tree works.

Draw the tree produced by list->tree for the list (1 3 5 7 9 11).
What is the order of growth in the number of steps required by list->tree to
convert a list of n elements?

Partial tree effectively performs binary search to split the tree. |#
(define (partial-tree elts n)
  (if (= n 0) (cons null elts)
      (let* ([left-size      (quotient (- n 1) 2)]
             [left-result    (partial-tree elts left-size)]
             [left-tree      (first left-result)]
             [right-elts     (rest left-result)]
             [right-size     (- n (+ left-size 1))]
             [this-entry     (first right-elts)]
             [right-result   (partial-tree (cdr right-elts)
                                           right-size)]
             [right-tree     (first right-result)]
             [remaining-elts (rest right-result)])

        (cons (node this-entry
                    left-tree
                    right-tree)
              remaining-elts))))

(define (list->tree elements)
  (car (partial-tree
        elements (length elements))))

(define tbsize 20)
(define tbset (make-random-bset tbsize))
(define tbbad (make-linear-bset tbsize))
(define tbsorted (list->tree (range tbsize)))
(define (nprint p)
  (pretty-print p (current-output-port) 1))


#|
def __str__(self, depth=0):
ret = ""

# Print right branch
if self.right != None:
ret += self.right.__str__(depth + 1)

# Print own value
ret += "\n" + ("    "*depth) + str(self.value)

# Print left branch
if self.left != None:
ret += self.left.__str__(depth + 1)

return ret
|#
(define (pprint tree [depth 0] [str ""])
  (string-append
   (if (empty? (node-left tree)) ""
       (string-append str (pprint (node-left tree) (+ 1 depth))))

    (string-append (make-string (* 2 depth) #\ ) str (number->string (node-val tree)) "\n")

   (if (empty? (node-right tree)) ""
       (string-append str (pprint (node-right tree) (+ 1 depth))))))

#|
Exercise 2.65: Use the results of Exercise 2.63 and Exercise 2.64 to give Θ ( n ) implementations of union-set and intersection-set for sets implemented as (balanced) binary trees.107
|#
(define (union-balanced-set bs1 bs2)
  (list->tree ((union-set (tree->list-1 bs1)
                          (tree->list-1 bs2)))))


(define (intersection-balanced-set bs1 bs2)
  (list->tree ((intersection (tree->list-1 bs1)
                             (tree->list-1 bs2)))))

#| Exercise 2.66
Implement the lookup procedure for the case where the set of records is
structured as a binary tree, ordered by the numerical values of the keys.
|#
(define (lookup-bset elt bs)
  (if (null? bs) false
      (let [(val (node-val bs))]
        (cond [(= val elt) bs]
              [(> val elt) (lookup-bset elt (node-left bs))]
              [(< val elt) (lookup-bset elt (node-right bs))]))))

#|
--Utility Functions-------------------------------------------------------------
|#

(struct leaf (sym weight)
  #:transparent)
(struct code-tree (left right syms weight)
  #:transparent)

(define (make-code-tree left right)
  (code-tree left
             right
             (append (syms left)
                     (syms right))
             (+ (weight left) (weight right))))

(define (left-branch tree) (code-tree-left tree))
(define (right-branch tree) (code-tree-right tree))

(define (syms tree)
  (if (leaf? tree)
      (list (leaf-sym tree))
      (code-tree-syms tree)))

(define (weight tree)
  (if (leaf? tree)
      (leaf-weight tree)
      (code-tree-weight tree)))

(define (decode bits tree)
  (define (decode-1 bits current-branch)
    (if (null? bits)
        null
        (let [(next-branch
               (choose-branch
                (car bits)
                current-branch))]
          (if (leaf? next-branch)
              (cons
               (leaf-sym next-branch)
               (decode-1 (cdr bits) tree))
              (decode-1 (cdr bits)
                        next-branch)))))
  (decode-1 bits tree))

(define (choose-branch bit branch)
  (cond [(= bit 0) (left-branch branch)]
        [(= bit 1) (right-branch branch)]
        [else (error "bad bit(ch?)")]))

(define (adjoin-htset x ss)
  (cond ((null? ss) (list x))
        ((< (weight x) (weight (car ss)))
         (cons x ss))
        (else
         (cons (car ss)
               (adjoin-htset x (cdr ss))))))

(define (make-leaf-set pairs)
  (if (null? pairs) null
      (let ((pair (car pairs)))
        (adjoin-htset
         (leaf (car pair)    ; symbol
               (cadr pair))  ; frequency
         (make-leaf-set (cdr pairs))))))

#|
--End of Utility Functions------------------------------------------------------
2.67: Define an encoding tree and a sample message:
|#
(define sample-tree
  (make-code-tree
   (leaf 'A 4)
   (make-code-tree
    (leaf 'B 2)
    (make-code-tree
     (leaf 'D 1)
     (leaf 'C 1)))))

;; A D A B B C A
(define sample-message
  '(0 1 1 0 0 1 0 1 0 1 1 1 0))

(define (decode-sample)
  (decode sample-message sample-tree)) ;; => '(A D A B B C A)

#| Exercise 2.68
The encode procedure takes as arguments a message and a tree and produces the
list of bits that gives the encoded message.

Encode-symbol is a procedure, which you must write, that returns the list of
bits that encodes a given symbol according to a given tree. You should design
encode-symbol so that it signals an error if the symbol is not in the tree at
all. Test your procedure by encoding the result you obtained in Exercise 2.67
with the sample tree and seeing whether it is the same as the original sample
message.
|#

(define (encode message tree)
  (if (null? message)
      '()
      (append
       (encode-symbol (car message)
                      tree)
       (encode (cdr message) tree))))

(define (encode-symbol symbol tree)
  (cond
    [(null? tree) (error "Not found")]
    [(leaf? tree) null]
    [(memq symbol (syms (left-branch tree)))
     (cons 0 (encode-symbol symbol (left-branch tree)))]
    [(memq symbol (syms (right-branch tree)))
     (cons 1 (encode-symbol symbol (right-branch tree)))]))

#| Exercise 2.69
The following procedure takes as its argument a list of symbol-frequency pairs
(where no symbol appears in more than one pair) and generates a Huffman encoding
tree according to the Huffman algorithm.

Make-leaf-set is the procedure given above that transforms the list of pairs
into an ordered set of leaves. Successive-merge is the procedure you must write,
using make-code-tree to successively merge the smallest-weight elements of the
set until there is only one element left, which is the desired Huffman tree.
(This procedure is slightly tricky, but not really complicated. If you find
yourself designing a complex procedure, then you are almost certainly doing
something wrong. You can take significant advantage of the fact that we are
using an ordered set representation.)
|#
(define (generate-huffman-tree pairs)
  (successive-merge
   (make-leaf-set pairs)))

(define (successive-merge xs)
  (if (= 1 (length xs)) (car xs)
      (successive-merge
       (cons (make-code-tree (cadr xs) (car xs))
             (cddr xs)))))

#| Exercise 2.70
The following eight-symbol alphabet with associated relative frequencies was
designed to efficiently encode the lyrics of 1950s rock songs. (Note that the
“symbols” of an “alphabet” need not be individual letters.)

    A    2    NA  16
    BOOM 1    SHA  3
    GET  2    YIP  9
    JOB  2    WAH  1

Use generate-huffman-tree (Exercise 2.69) to generate a corresponding Huffman
tree, and use encode (Exercise 2.68) to encode the following message:

    Get a job
    Sha na na na na na na na na

    Get a job
    Sha na na na na na na na na

    Wah yip yip yip yip
    yip yip yip yip yip
    Sha boom
|#

(define (generate-rock-n-roll-htree)
  (define rockfreq (generate-huffman-tree
                    '((A 2)    (NA  16)
                      (BOOM 1) (SHA  3)
                      (GET  2) (YIP  9)
                      (JOB  2) (WAH  1))))
  (define msg-to-youth
    (map (λ (s) (string->symbol (string-upcase s)))
         (string-split "Get a job Sha na na na na na na na na
                        Get a job Sha na na na na na na na na Wah yip yip
                        yip yip yip yip yip yip yip Sha boom")))
  (define rock-bits (encode msg-to-youth rockfreq))
  (printf "bits: ~a\n\n" rock-bits)
  (printf "decoded: ~a\n" (decode rock-bits rockfreq)))

#|
Exercise 2.72
Consider the encoding procedure that you designed in Exercise 2.68. What is the
order of growth in the number of steps needed to encode a symbol? Be sure to
include the number of steps needed to search the symbol list at each node
encountered. To answer this question in general is difficult. Consider the
special case where the relative frequencies of the n symbols are as described in
Exercise 2.71, and give the order of growth (as a function of n ) of the number
of steps needed to encode the most frequent and least frequent symbols in the
alphabet.
|#

;; Answer:
;; (Copied from Eli Bendersky)

;; In general, in the worst case we’d need to descend n levels (as Exercise 2.71
;; shows), and at each step we have to find the symbol in a set of symbols at that
;; node. The implementation of encode used an unordered set to keep the symbols, so
;; the search takes O(n)[3]. Therefore, the whole encoding procedure takes O(n^2).
;; Had we used a binary tree for the sets of symbols, we could bring this time down
;; to O(n^2). Of course, building the tree would then take longer.

;; --------------------------------------------------
;; Section 2.4
;; --------------------------------------------------

#| Exercise 2.73
2.3.2 described a program that performs symbolic differentiation:

(define (deriv exp var)
  (cond ((number? exp) 0)
        ((variable? exp)
         (if (same-variable? exp var) 1 0))
        ((sum? exp)
         (make-sum (deriv (addend exp) var)
                   (deriv (augend exp) var)))
        ((product? exp)
         (make-sum
           (make-product
            (multiplier exp)
            (deriv (multiplicand exp) var))
           (make-product
            (deriv (multiplier exp) var)
            (multiplicand exp))))
        ⟨more rules can be added here⟩
        (else (error "unknown expression type:
                      DERIV" exp))))

We can regard this program as performing a dispatch on the type of the
expression to be differentiated. In this situation the “type tag” of the datum
is the algebraic operator symbol (such as +) and the operation being performed
is deriv. We can transform this program into data-directed style by rewriting
the basic derivative procedure as

(define (deriv exp var)
   (cond ((number? exp) 0)
         ((variable? exp)
           (if (same-variable? exp var)
               1
               0))
         (else ((get 'deriv (operator exp))
                (operands exp)
                var))))

(define (operator exp) (car exp))
(define (operands exp) (cdr exp))

(define (deriv exp var)
   (cond ((number? exp) 0)
         ((variable? exp)
           (if (same-variable? exp var)
               1
               0))
         (else ((get 'deriv (operator exp))
                (operands exp)
                var))))

(define (operator exp) (car exp))
(define (operands exp) (cdr exp))

  1. Explain what was done above. Why can’t we assimilate the predicates number?
and variable? into the data-directed dispatch?

The procedures are now being dispatched on the type of the tag -- It would be meaningless to integrate predicates into a data-driven programming method -- They are the first-order methods.

  2. Write the procedures for derivatives of sums and products, and the auxiliary
code required to install them in the table used by the program above.

  3. Choose any additional differentiation rule that you like, such as the one for
exponents (Exercise 2.56), and install it in this data-directed system.

  4. In this simple algebraic manipulator the type of an expression is the
algebraic operator that binds it together. Suppose, however, we indexed the
procedures in the opposite way, so that the dispatch line in deriv looked like

    ((get (operator exp) 'deriv)
     (operands exp) var)

What corresponding changes to the derivative system are required?
|#
;; TODO BORING

#| Exercise 2.75
Implement the constructor make-from-mag-ang in message-passing style. This
procedure should be analogous to the make-from-real-imag procedure given above.
|#

(define (make-from-mag-ang magnitude angle)
  (define (dispatch op)
    (cond [(eq? op 'magnitude) magnitude]
          [(eq? op 'angle) angle]
          [(eq? op 'real-part)
           (* magnitude (cos angle))]
          [(eq? op 'imag-part)
           (* magnitude (sin angle))]
          [else (error "you fucked up")]))
  dispatch)


#| Exercise 2.76

As a large system with generic operations evolves, new types of data objects or
new operations may be needed. For each of the three strategies—generic
operations with explicit dispatch, data-directed style, and
message-passing-style—describe the changes that must be made to a system in
order to add new types or new operations. Which organization would be most
appropriate for a system in which new types must often be added? Which would be
most appropriate for a system in which new operations must often be added?
|#

;;
;; | System         | Changes                                                          |
;; -------------------------------------------------------------------------------------
;; Direct           | New functions must be added, existing dispatch functions must
;;                    introduce the new behaviour manually or modify the existing
;;                    code to suit new datatypes

;; Data Directed    | Each new function must be "registered" in the table of
;;                    dispatch-functions, if a data type changes, existing predicates
;;                    and selectors must compute their values in terms of
;;                    new structure elements

;; Message Passing  | The function/module that provides the representation of
;;                    data structure must have functions added to it, existing
;;                    functions are to new behaviour directly if possible.

;; --------------------------------------------------
;; Section 2.5
;; --------------------------------------------------
(module number-package racket
  (provide add)
  (provide sub)
  (provide mul)
  (provide div)

  (define generics-table (make-hash))

  (define (mk-opname op type-tag)
    "Make the name used in the hash table to refer to the operation and type"
    (printf "~a~a" op type-tag))
  (define (put op type-tag item)
    "Install an operation into the generic functions table"
    (hash-set! generics-table (mk-opname "~a~a" op type-tag) item))
  (define (get op type-tag)
    "Find a function in the generics function table"
    (hash-ref generics-table (mk-opname op type-tag)))

  (define (apply-generic op args)
    (let* ([type-tags (map type-tag args)]
           [proc (get op type-tags)])
        (if proc
            (apply proc (map contents args))
            (error
             "No method for these types:
             APPLY-GENERIC"
             (list op type-tags)))))

  (define (add x y) (apply-generic 'add x y))
  (define (sub x y) (apply-generic 'sub x y))
  (define (mul x y) (apply-generic 'mul x y))
  (define (div x y) (apply-generic 'div x y))
  )
#| Exercise: 2.5
|#
(define lower-expt 2)
(define higher-expt 5)
(define (pack-pair a b)
  (* (expt lower-expt a)
     (expt higher-expt b)))

(define (unpack-base x base)
  (if [= 0 (remainder x base)]
      (+ 1 (unpack-base (/ x base) base))
      0))

(define (unpack-pair d)
  `(,(unpack-base d lower-expt)
    ,(unpack-base d higher-expt)))

