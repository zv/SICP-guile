;; -*- mode: racket; fill-column: 75; comment-column: 50; coding: utf-8; -*-
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
Define a better version of `make-rat' that handles both positive and
negative arguments. `Make-rat' should normalize the sign so that if the
rational number is positive, both the numerator and denominator are
positive, and if the rational number is negative, only the numerator is
negative.
|#
(define (make-rat n d)
  (let* [(g (abs (gcd n d)))
         (nsign (xor (negative? d)
                    (negative? n)))
         (num (/ (abs n) g))
         (den (/ (abs d) g))]
    (if nsign (cons (* -1 num) den)
        (cons num den))))

#| Exercise: 2.2
Consider the problem of representing line segments in a plane. Each segment
is represented as a pair of points: a starting point and an ending point.
Define a constructor `make-segment' and selectors `start-segment' and
`end-segment' that define the representation of segments in terms of
points. Furthermore, a point can be represented as a pair of numbers: the x
coordinate and the y coordinate. Accordingly, specify a constructor
`make-point' and selectors `x-point' and `y-point' that define this
representation. Finally, using your selectors and constructors, define a
procedure `midpoint-segment' that takes a line segment as argument and
returns its midpoint (the point whose coordinates are the average of the
coordinates of the endpoints). To try your procedures, you'll need a way to
print points:

    (define (print-point p)
      (newline)
      (display "(")
      (display (x-point p))
      (display ",")
      (display (y-point p))
      (display ")"))

|#
(struct coordinate (x y) #:transparent)
(struct segment (start end) #:transparent)

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

#| Exercise 2.3
Implement a representation for rectangles in a plane. (Hint: You may want
to make use of *Note Exercise 2-2::.) In terms of your constructors and
selectors, create procedures that compute the perimeter and the area of a
given rectangle. Now implement a different representation for rectangles.
Can you design your system with suitable abstraction barriers, so that the
same perimeter and area procedures will work using either representation?
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

#| Exercise: 2.4
Here is an alternative procedural representation
of pairs.  For this representation, verify that `(car (cons x y))'
yields `x' for any objects `x' and `y'.

(define (cons x y)
  (lambda (m) (m x y)))

(define (car z)
  (z (lambda (p q) p)))

What is the corresponding definition of `cdr'? (Hint: To verify that this
works, make use of the substitution model of section *Note 1-1-5.)

|#
;;; whoa!!!
(define (recons x y)
  (λ (m) (m x y)))

(define (recar z)
  (z (λ (p q) p)))

(define (recdr z)
  (z (λ (p q) q)))


#| Exercise: 2.5
Show that we can represent pairs of nonnegative integers using only numbers
and arithmetic operations if we represent the pair a and b as the integer
that is the product 2^a 3^b. Give the corresponding definitions of the
procedures `cons', `car', and `cdr'.
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

#| Exercise: 2.6
In case representing pairs as procedures wasn't mind-boggling enough,
consider that, in a language that can manipulate procedures, we can get by
without numbers (at least insofar as nonnegative integers are concerned) by
implementing 0 and the operation of adding 1 as

(define zero (lambda (f) (lambda (x) x)))
|#
(define church-zero (λ (f) (λ (x) x)))

(define (church-add-1 n)
  (λ (f) (λ (x) (f ((n f) x)))))

(define church-one
  (λ (f)
    (λ (x)
      (f x))))

(define church-two
  (λ (f)
    (λ (x)
      (f
       (f x)))))

(define (church-addition m n)
  (λ (f)
    (λ (x)
      ((n f)
       ((m f)
        x)))))


#| Exercise: 2.7
Alyssa's program is incomplete because she has not specified the
implementation of the interval abstraction. Here is a definition of the
interval constructor:

(define (make-interval a b) (cons a b))

Define selectors `upper-bound' and `lower-bound' to complete the
implementation.
|#
;; (module interval racket
;;   (provide add-interval mul-interval div-interval)
;;   (define (add-interval x y)
;;     (make-interval (+ (lower-bound x) (lower-bound y))
;;                    (+ (upper-bound x) (upper-bound y))))
;;   )

(define (make-interval a b) (cons a b))
(define (upper-bound interval) (cdr interval))
(define (lower-bound interval) (car interval))

#| Exercise: 2.8
Using reasoning analogous to Alyssa's, describe how the difference of two
intervals may be computed. Define a corresponding subtraction procedure,
called `sub-interval'.
|#
(define (sub-interval x y)
  (let ((p1 (- (lower-bound x) (lower-bound y)))
        (p2 (- (lower-bound y) (upper-bound x))))
    (make-interval (min p1 p2)
                   (max p1 p2))))

#| Exercise: 2.9
The "width" of an interval is half of the difference between its upper and
lower bounds. The width is a measure of the uncertainty of the number
specified by the interval. For some arithmetic operations the width of the
result of combining two intervals is a function only of the widths of the
argument intervals, whereas for others the width of the combination is not
a function of the widths of the argument intervals. Show that the width of
the sum (or difference) of two intervals is a function only of the widths
of the intervals being added (or subtracted). Give examples to show that
this is not true for multiplication or division.
|#

#| Exercise: 2.10
Ben Bitdiddle, an expert systems programmer, looks over Alyssa's shoulder
and comments that it is not clear what it means to divide by an interval
that spans zero. Modify Alyssa's code to check for this condition and to
signal an error if it occurs.
|#
(define (div-interval x y)
  (cond ((or (= 0 (upper-bound y)) (= 0 (lower-bound y)))
         (error "attempted to divide by the zero"))
        (else (mul-interval x
                            (make-interval (/ 1.0 (upper-bound y))
                                           (/ 1.0 (lower-bound y)))))))

#| Exercise: 2.11
In passing, Ben also cryptically comments: "By testing the signs of the
endpoints of the intervals, it is possible to break `mul-interval' into
nine cases, only one of which requires more than two multiplications."
Rewrite this procedure using Ben's suggestion.

After debugging her program, Alyssa shows it to a potential user, who
complains that her program solves the wrong problem. He wants a program
that can deal with numbers represented as a center value and an additive
tolerance; for example, he wants to work with intervals such as 3.5 +/-
0.15 rather than [3.35, 3.65]. Alyssa returns to her desk and fixes this
problem by supplying an alternate constructor and alternate selectors:

(define (make-center-width c w) (make-interval (- c w) (+ c w)))

(define (center i) (/ (+ (lower-bound i) (upper-bound i)) 2))

(define (width i) (/ (- (upper-bound i) (lower-bound i)) 2))

Unfortunately, most of Alyssa's users are engineers. Real engineering
situations usually involve measurements with only a small uncertainty,
measured as the ratio of the width of the interval to the midpoint of the
interval. Engineers usually specify percentage tolerances on the parameters
of devices, as in the resistor specifications given earlier.
|#
 (define (mul-interval x y)
  (let ((p1 (* (lower-bound x) (lower-bound y)))
        (p2 (* (lower-bound x) (upper-bound y)))
        (p3 (* (upper-bound x) (lower-bound y)))
        (p4 (* (upper-bound x) (upper-bound y))))
    (make-interval (min p1 p2 p3 p4)
                   (max p1 p2 p3 p4))))

#| Exercise: 2.17
Define a procedure `last-pair' that returns the list that contains only the
last element of a given (nonempty) list:

(last-pair (list 23 72 149 34)) (34)
|#
(define (last-pair lst)
  (let [(lastls (cdr lst))]
    (if (null? lastls) (car lst)
        (last-pair lastls))))

#| Exercise: 2.18
Define a procedure `reverse' that takes a list as argument and returns a
list of the same elements in reverse order:

(reverse (list 1 4 9 16 25)) (25 16 9 4 1)
|#
(define (reverse-l lst)
  (if (null? lst) null
      (append (reverse-l (cdr lst)) (list (car lst)))))

(define (reverse-ls xs [result null])
  (cond [(null? xs) result]
        [else (reverse-ls (cdr xs) (cons (car xs) result))]))

#| Exercise: 2.19
Consider the change-counting program of section *Note 1-2-2::. It would be
nice to be able to easily change the currency used by the program, so that
we could compute the number of ways to change a British pound, for example.
As the program is written, the knowledge of the currency is distributed
partly into the procedure `first-denomination' and partly into the
procedure `count-change' (which knows that there are five kinds of U.S.
coins). It would be nicer to be able to supply a list of coins to be used
for making change.

We want to rewrite the procedure `cc' so that its second argument is a list
of the values of the coins to use rather than an integer specifying which
coins to use. We could then have lists that defined each kind of currency:

(define us-coins (list 50 25 10 5 1))

(define uk-coins (list 100 50 20 10 5 2 1 0.5))

We could then call `cc' as follows:

(cc 100 us-coins) 292

To do this will require changing the program `cc' somewhat. It will still
have the same form, but it will access its second argument differently, as
follows:

(define (cc amount coin-values) (cond ((= amount 0) 1) ((or (< amount 0)
(no-more? coin-values)) 0) (else (+ (cc amount (except-first-denomination
coin-values)) (cc (- amount (first-denomination coin-values))
coin-values)))))

Define the procedures `first-denomination', `except-first-denomination',
and `no-more?' in terms of primitive operations on list structures. Does
the order of the list `coin-values' affect the answer produced by `cc'? Why
or why not?
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
The procedures `+', `*', and `list' take arbitrary numbers of arguments.
One way to define such procedures is to use `define' with notation
"dotted-tail notation". In a procedure definition, a parameter list that
has a dot before the last parameter name indicates that, when the procedure
is called, the initial parameters (if any) will have as values the initial
arguments, as usual, but the final parameter's value will be a "list" of
any remaining arguments. For instance, given the definition

(define (f x y . z) <BODY>)

the procedure `f' can be called with two or more arguments. If we evaluate

(f 1 2 3 4 5 6)

then in the body of `f', `x' will be 1, `y' will be 2, and `z' will be the
list `(3 4 5 6)'. Given the definition

(define (g . w) <BODY>)

the procedure `g' can be called with zero or more arguments. If we evaluate

(g 1 2 3 4 5 6)

then in the body of `g', `w' will be the list `(1 2 3 4 5 6)'.(4)

Use this notation to write a procedure `same-parity' that takes one or more
integers and returns a list of all the arguments that have the same
even-odd parity as the first argument. For example,

(same-parity 1 2 3 4 5 6 7) (1 3 5 7)

(same-parity 2 3 4 5 6 7) (2 4 6)
|#

(define (same-parity elt . xs)
  (define (test-parity n) (= (remainder elt 2) (remainder n 2)))
  (filter test-parity xs))


#| Exercise: 2.21
The procedure `square-list' takes a list of numbers as argument and returns
a list of the squares of those numbers.

(square-list (list 1 2 3 4)) (1 4 9 16)

Here are two different definitions of `square-list'. Complete both of them
by filling in the missing expressions:

(define (square-list items) (if (null? items) nil (cons <??> <??>)))

(define (square-list items) (map <??> <??>))
|#
(define (square n) (* n n))

(define (square-list items)
  (if (null? items) null
      (cons (square (car items)) (square-list (cdr items)))))

(define (square-list-x items)
  (map square items))

#| Exercise: 2.22
Louis Reasoner tries to rewrite the first `square-list' procedure of *Note
Exercise 2-21:: so that it evolves an iterative process:

  (define (square-list items) (define (iter things answer) (if (null?
things) answer (iter (cdr things) (cons (square (car things)) answer))))
(iter items nil))

Unfortunately, defining `square-list' this way produces the answer list in
the reverse order of the one desired. Why?

Louis then tries to fix his bug by interchanging the arguments to `cons':

(define (square-list items) (define (iter things answer) (if (null? things)
answer (iter (cdr things) (cons answer (square (car things)))))) (iter
items nil))

This doesn't work either. Explain.
|#
;;; Louis Reasoner has mixed up the arguments `answer' and `(square (car things))'
;;; In his second attempt
;; correct version of iterative
;; (define (square-list-b things [answer null])
;;     (if (null? things) answer
;;         (square-list-b (cdr things)
;;                        (append answer (list (square (car things)))))))

#| Exercise: 2.23
The procedure `for-each' is similar to `map'. It takes as arguments a
procedure and a list of elements. However, rather than forming a list of
the results, `for-each' just applies the procedure to each of the elements
in turn, from left to right. The values returned by applying the procedure
to the elements are not used at all--`for-each' is used with procedures
that perform an action, such as printing. For example,

(for-each (lambda (x) (newline) (display x)) (list 57 321 88)) 57 321 88

The value returned by the call to `for-each' (not illustrated above) can be
something arbitrary, such as true. Give an implementation of `for-each'.
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
Suppose we evaluate the expression `(list 1 (list 2 (list 3 4)))'. Give the
result printed by the interpreter, the corresponding box-and-pointer
structure, and the interpretation of this as a tree (as in *Note Figure
2-6::).
|#

#| Exercise: 2.25
Give combinations of `car's and `cdr's that will pick 7 from each of the
following lists:

(1 3 (5 7) 9)

((7))

(1 (2 (3 (4 (5 (6 7))))))
|#
(define (is-sevens)
  [ printf "~a\n" (car (cdaddr '(1 3 (5 7) 9)))]
  [ printf "~a\n" (caar '((7)))]
  [ printf "~a\n" (cadadr (cadadr (cadadr '(1 (2 (3 (4 (5 (6 7)))))))))])

#| Exercise: 2.26
Suppose we define `x' and `y' to be two lists:

(define x (list 1 2 3))

(define y (list 4 5 6))

What result is printed by the interpreter in response to evaluating each of
the following expressions:

(append x y)

(cons x y)

(list x y)
|#
(define two-twentysix-x (list 1 2 3))
(define two-twentysix-y (list 4 5 6))
;;; (append two-twentysix-x two-twentysix-y) => '(1 2 3 4 5 6)
;;; (cons two-twentysix-x two-twentysix-y)   => '((1 2 3) 4 5 6)
;;;  (list two-twentysix-x two-twentysix-y)  => '((1 2 3) (4 5 6))

#| Exercise: 2.27
Modify your `reverse' procedure of *Note Exercise 2-18:: to produce a
`deep-reverse' procedure that takes a list as argument and returns as its
value the list with its elements reversed and with all sublists
deep-reversed as well. For example,

(define x (list (list 1 2) (list 3 4)))

x ((1 2) (3 4))

(reverse x) ((3 4) (1 2))

(deep-reverse x) ((4 3) (2 1))
|#
(define (deep-reverse-l lst)
  (cond [(null? lst) null]
        [(list? lst) (append
                      (deep-reverse-l (rest lst))
                      (list (deep-reverse-l (first lst))))]
        [else lst]))

#| Exercise: 2.28
Write a procedure `fringe' that takes as argument a tree (represented as a
list) and returns a list whose elements are all the leaves of the tree
arranged in left-to-right order. For example,

(define x (list (list 1 2) (list 3 4)))

(fringe x) (1 2 3 4)

(fringe (list x x)) (1 2 3 4 1 2 3 4)
|#
(define (fringe xs)
  (cond [(null? xs) null]
        [(list? xs) (append (fringe (first xs))
                            (fringe (rest xs)))]
        [else (list xs)]))


#| Exercise: 2.29
A binary mobile consists of two branches, a left branch and a right branch.
Each branch is a rod of a certain length, from which hangs either a weight
or another binary mobile. We can represent a binary mobile using compound
data by constructing it from two branches (for example, using `list'):

(define (make-mobile left right) (list left right))

A branch is constructed from a `length' (which must be a number) together
with a `structure', which may be either a number (representing a simple
weight) or another mobile:

(define (make-branch length structure) (list length structure))

a. Write the corresponding selectors `left-branch' and `right-branch',
which return the branches of a mobile, and `branch-length' and
`branch-structure', which return the components of a branch.

b. Using your selectors, define a procedure `total-weight' that returns the
total weight of a mobile.

c. A mobile is said to be "balanced" if the torque applied by its top-left
branch is equal to that applied by its top-right branch (that is, if the
length of the left rod multiplied by the weight hanging from that rod is
equal to the corresponding product for the right side) and if each of the
submobiles hanging off its branches is balanced. Design a predicate that
tests whether a binary mobile is balanced.

d. Suppose we change the representation of mobiles so that the constructors
are

(define (make-mobile left right) (cons left right))

(define (make-branch length structure) (cons length structure))

How much do you need to change your programs to convert to the new
representation?
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
Define a procedure `square-tree' analogous to the `square-list' procedure
of *Note Exercise 2-21::. That is, `square-list' should behave as follows:

(square-tree (list 1 (list 2 (list 3 4) 5) (list 6 7))) (1 (4 (9 16) 25)
(36 49))

Define `square-tree' both directly (i.e., without using any higher-order
procedures) and also by using `map' and recursion.
|#
(define (square-tree tree)
  (map (λ (node)
         (if (list? node) (square-tree node)
             (* node node))) tree))
#| Exercise: 2.31
Abstract your answer to *Note Exercise 2-30:: to produce a procedure
`tree-map' with the property that `square-tree' could be defined as

(define (square-tree tree) (tree-map square tree))

We can represent a set as a list of distinct elements, and we can represent
the set of all subsets of the set as a list of lists. For example, if the
set is `(1 2 3)', then the set of all subsets is `(() (3) (2) (2 3) (1) (1
3) (1 2) (1 2 3))'. Complete the following definition of a procedure that
generates the set of subsets of a set and give a clear explanation of why
it works:

(define (subsets s) (if (null? s) (list nil) (let ((rest (subsets (cdr
s)))) (append rest (map <??> rest)))))
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
      (list null)                  ; sequence containing empty set
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
Evaluating a polynomial in x at a given value of x can be formulated as an
accumulation. We evaluate the polynomial

a_n r^n | a_(n-1) r^(n-1) + ... + a_1 r + a_0

using a well-known algorithm called "Horner's rule", which structures the
computation as

(... (a_n r + a_(n-1)) r + ... + a_1) r + a_0

In other words, we start with a_n, multiply by x, add a_(n-1), multiply by
x, and so on, until we reach a_0.(3)

Fill in the following template to produce a procedure that evaluates a
polynomial using Horner's rule. Assume that the coefficients of the
polynomial are arranged in a sequence, from a_0 through a_n.

(define (horner-eval x coefficient-sequence) (accumulate (lambda
(this-coeff higher-terms) <??>) 0 coefficient-sequence))

For example, to compute 1 + 3x + 5x^3 + x^(5) at x = 2 you would evaluate

(horner-eval 2 (list 1 3 0 5 0 1))
|#
(define (horner-eval x coefficient-sequence)
  (accumulate (λ (this-coeff higher-terms)
                (+ this-coeff (* x higher-terms)))
              0
              coefficient-sequence))


#| Exercise: 2.35
Redefine `count-leaves' from section *Note 2-2-2:: as an accumulation:

(define (count-leaves t) (accumulate <??> <??> (map <??> <??>)))
|#
(define (count-leaves-z t)
  (accumulate + 0 (map count-leaves t)))

#| Exercise: 2.36
The procedure `accumulate-n' is similar to `accumulate' except that it
takes as its third argument a sequence of sequences, which are all assumed
to have the same number of elements. It applies the designated accumulation
procedure to combine all the first elements of the sequences, all the
second elements of the sequences, and so on, and returns a sequence of the
results. For instance, if `s' is a sequence containing four sequences, `((1
2 3) (4 5 6) (7 8 9) (10 11 12)),' then the value of `(accumulate-n + 0 s)'
should be the sequence `(22 26 30)'. Fill in the missing expressions in the
following definition of `accumulate-n':

(define (accumulate-n op init seqs) (if (null? (car seqs)) nil (cons
(accumulate op init <??>) (accumulate-n op init <??>))))
|#
(define (accumulate-n op ini seqs)
  (if (null? (car seqs))
      null
      (cons (accumulate op ini (map (lambda (x) (car x)) seqs))
            (accumulate-n op ini (map (lambda (x) (cdr x)) seqs)))))

#| Exercise: 2.37
Exercise 2.37 .............

Suppose we represent vectors v = (v_i) as sequences of numbers, and
matrices m = (m_(ij)) as sequences of vectors (the rows of the matrix). For
example, the matrix

+- -+ | 1 2 3 4 | | 4 5 6 6 | | 6 7 8 9 | +- -+

is represented as the sequence `((1 2 3 4) (4 5 6 6) (6 7 8 9))'. With this
representation, we can use sequence operations to concisely express the
basic matrix and vector operations. These operations (which are described
in any book on matrix algebra) are the following:

__ (dot-product v w) returns the sum >_i v_i w_i

(matrix-*-vector m v) returns the vector t, __ where t_i = >_j m_(ij) v_j

(matrix-*-matrix m n) returns the matrix p, __ where p_(ij) = >_k m_(ik)
n_(kj)

(transpose m) returns the matrix n, where n_(ij) = m_(ji)

We can define the dot product as(4)

(define (dot-product v w) (accumulate + 0 (map * v w)))

Fill in the missing expressions in the following procedures for computing
the other matrix operations. (The procedure `accumulate-n' is defined in
*Note Exercise 2-36::.)

(define (matrix-*-vector m v) (map <??> m))

(define (transpose mat) (accumulate-n <??> <??> mat))

(define (matrix-*-matrix m n) (let ((cols (transpose n))) (map <??> m)))
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
The `accumulate' procedure is also known as `fold-right', because it
combines the first element of the sequence with the result of combining all
the elements to the right. There is also a `fold-left', which is similar to
`fold-right', except that it combines elements working in the opposite
direction:

(define (fold-left op initial sequence) (define (iter result rest) (if
(null? rest) result (iter (op result (car rest)) (cdr rest)))) (iter
initial sequence))

What are the values of

(fold-right / 1 (list 1 2 3))

(fold-left / 1 (list 1 2 3))

(fold-right list nil (list 1 2 3))

(fold-left list nil (list 1 2 3))

Give a property that `op' should satisfy to guarantee that `fold-right' and
`fold-left' will produce the same values for any sequence.
|#
;;;; skipped

#| Exercise: 2.39
Complete the following definitions of `reverse' (*Note Exercise 2-18::) in
terms of `fold-right' and `fold-left' from *Note Exercise 2-38:::

(define (reverse sequence) (fold-right (lambda (x y) <??>) nil sequence))

(define (reverse sequence) (fold-left (lambda (x y) <??>) nil sequence))
|#
(define (reverse-fr sequence)
  (foldr (lambda (x y) (append y `(,x))) null sequence))

(define (reverse-fl sequence)
  (foldl (lambda (x y) (cons x y)) null sequence))

#| Exercise: 2.40
Define a procedure `unique-pairs' that, given an integer n, generates the
sequence of pairs (i,j) with 1 <= j< i <= n. Use `unique-pairs' to simplify
the definition of `prime-sum-pairs' given above.
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
Write a procedure to find all ordered triples of distinct positive integers
i, j, and k less than or equal to a given integer n that sum to a given
integer s.
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
The "eight-queens puzzle" asks how to place eight queens on a chessboard so
that no queen is in check from any other (i.e., no two queens are in the
same row, column, or diagonal). One possible solution is shown in *Note
Figure 2-8. One way to solve the puzzle is to work across the board,
placing a queen in each column. Once we have placed k - 1 queens, we must
place the kth queen in a position where it does not check any of the queens
already on the board. We can formulate this approach recursively: Assume
that we have already generated the sequence of all possible ways to place k
- 1 queens in the first k - 1 columns of the board. For each of these ways,
generate an extended set of positions by placing a queen in each row of the
kth column. Now filter these, keeping only the positions for which the
queen in the kth column is safe with respect to the other queens. This
produces the sequence of all ways to place k queens in the first k columns.
By continuing this process, we will produce not only one solution, but all
solutions to the puzzle.

We implement this solution as a procedure `queens', which returns a
sequence of all solutions to the problem of placing n queens on an n*n
chessboard. `Queens' has an internal procedure `queen-cols' that returns
the sequence of all ways to place queens in the first k columns of the
board.

(define (queens board-size) (define (queen-cols k) (if (= k 0) (list
empty-board) (filter (lambda (positions) (safe? k positions)) (flatmap
(lambda (rest-of-queens) (map (lambda (new-row) (adjoin-position new-row k
rest-of-queens)) (enumerate-interval 1 board-size))) (queen-cols (- k
1)))))) (queen-cols board-size))

In this procedure `rest-of-queens' is a way to place k - 1 queens in the
first k - 1 columns, and `new-row' is a proposed row in which to place the
queen for the kth column. Complete the program by implementing the
representation for sets of board positions, including the procedure
`adjoin-position', which adjoins a new row-column position to a set of
positions, and `empty-board', which represents an empty set of positions.
You must also write the procedure `safe?', which determines for a set of
positions, whether the queen in the kth column is safe with respect to the
others. (Note that we need only check whether the new queen is safe--the
other queens are already guaranteed safe with respect to each other.)
|#
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
What would the interpreter print in response to evaluating each of the
following expressions?

(list 'a 'b 'c)

(list (list 'george))

(cdr '((x1 x2) (y1 y2)))

(cadr '((x1 x2) (y1 y2)))

(pair? (car '(a short list)))

(memq 'red '((red shoes) (blue socks)))

(memq 'red '(red shoes blue socks))
|#

;;; (list 'a 'b 'c)                         => '(a b c)
;;; (list (list 'george))                   => '((georger))
;;; (cdr '((x1 x2) (y1 y2)))                => '(y1 y2)
;;; (cadr '((x1 x2) (y1 y2)))               => '(y1 y2)
;;; (pair? (car '(a short list)))           => 'a
;;; (memq 'red '((red shoes) (blue socks))) => null
;;; (memq 'red '(red shoes blue socks))     => '(shoes blue socks)

#| Exercise: 2.54
Two lists are said to be `equal?' if they contain equal elements arranged
in the same order. For example,

(equal? '(this is a list) '(this is a list))

is true, but

(equal? '(this is a list) '(this (is a) list))

is false. To be more precise, we can define `equal?' recursively in terms
of the basic `eq?' equality of symbols by saying that `a' and `b' are
`equal?' if they are both symbols and the symbols are `eq?', or if they are
both lists such that `(car a)' is `equal?' to `(car b)' and `(cdr a)' is
`equal?' to `(cdr b)'. Using this idea, implement `equal?' as a
procedure.(5)

|#
(define (zv-equal? a b)
  (cond [(or (empty? a) (empty? b)) (eq? a b)]
        [(and (list? a) (list? b))
         (and (eq? (car a) (car b))
              (zv-equal? (cdr a) (cdr b)))]
        [(or (list? a) (list? b)) false]
        [else (eq? a b)]))

#| Exercise: 2.55
Eva Lu Ator types to the interpreter the expression

(car ''abracadabra)

To her surprise, the interpreter prints back `quote'. Explain.
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
Show how to extend the basic differentiator to handle more kinds of
expressions. For instance, implement the differentiation rule

n_1 n_2 --- = --- if and only if n_1 d_2 = n_2 d_1 d_1 d_2

by adding a new clause to the `deriv' program and defining appropriate
procedures `exponentiation?', `base', `exponent', and
`make-exponentiation'. (You may use the symbol `**' to denote
exponentiation.) Build in the rules that anything raised to the power 0 is
1 and anything raised to the power 1 is the thing itself.
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
Extend the differentiation program to handle sums and products of arbitrary
numbers of (two or more) terms. Then the last example above could be
expressed as

(deriv '(* x y (+ x 3)) 'x)

Try to do this by changing only the representation for sums and products,
without changing the `deriv' procedure at all. For example, the `addend' of
a sum would be the first term, and the `augend' would be the sum of the
rest of the terms.
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
Suppose we want to modify the differentiation program so that it works with
ordinary mathematical notation, in which `+' and `*' are infix rather than
prefix operators. Since the differentiation program is defined in terms of
abstract data, we can modify it to work with different representations of
expressions solely by changing the predicates, selectors, and constructors
that define the representation of the algebraic expressions on which the
differentiator is to operate.

a. Show how to do this in order to differentiate algebraic expressions
presented in infix form, such as `(x + (3 * (x + (y + 2))))'. To simplify
the task, assume that `+' and `*' always take two arguments and that
expressions are fully parenthesized.

b. The problem becomes substantially harder if we allow standard algebraic
notation, such as `(x + 3 * (x + y + 2))', which drops unnecessary
parentheses and assumes that multiplication is done before addition. Can
you design appropriate predicates, selectors, and constructors for this
notation such that our derivative program still works?


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
Implement the `union-set' operation for the unordered-list representation
of sets.
|#
(define (union-set ss1 ss2)
  (cond [(or (empty? ss1) (empty? ss2)) (append ss1 ss2)]
        [(element-of-set? (car ss1) ss2)
         (union-set (cdr ss1) ss2)]
        [else
         (cons (car ss1) (union-set (cdr ss1) ss2))]))

#| Exercise: 2.60
We specified that a set would be represented as a list with no duplicates.
Now suppose we allow duplicates. For instance, the set {1,2,3} could be
represented as the list `(2 3 2 1 3 2 2)'. Design procedures
`element-of-set?', `adjoin-set', `union-set', and `intersection-set' that
operate on this representation. How does the efficiency of each compare
with the corresponding procedure for the non-duplicate representation? Are
there applications for which you would use this representation in
preference to the non-duplicate one?
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
Give an implementation of `adjoin-set' using the ordered representation. By
analogy with `element-of-set?' show how to take advantage of the ordering
to produce a procedure that requires on the average about half as many
steps as with the unordered representation.
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
Give a [theta](n) implementation of `union-set' for sets represented as
ordered lists.
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
Each of the following two procedures converts a binary tree to a list.

(define (tree->list-1 tree)
  (if (null? tree)
      '()
      (append (tree->list-1 (left-branch tree))
              (cons (entry tree)
                    (tree->list-1 (right-branch tree))))))

(define (tree->list-2 tree)
  (define (copy-to-list tree result-list)
    (if (null? tree)
        result-list
        (copy-to-list (left-branch tree)
                      (cons (entry tree)
                            (copy-to-list (right-branch tree)
                                          result-list)))))
  (copy-to-list tree '()))

a. Do the two procedures produce the same result for every tree?
If not, how do the results differ?  What lists do the two
procedures produce for the trees in *Note Figure 2-16::?

b. Do the two procedures have the same order of growth in the
number of steps required to convert a balanced tree with n
elements to a list?  If not, which one grows more slowly?
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

#| Exercise 2.65
Use the results of Exercise 2.63 and Exercise 2.64 to give Θ ( n )
implementations of union-set and intersection-set for sets implemented as
(balanced) binary trees.107
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

#| Exercise 2.67:
Define an encoding tree and a sample message:

(define sample-tree
  (make-code-tree (make-leaf 'A 4)
                  (make-code-tree
                   (make-leaf 'B 2)
                   (make-code-tree (make-leaf 'D 1)
                                   (make-leaf 'C 1)))))

(define sample-message '(0 1 1 0 0 1 0 1 0 1 1 1 0))

Use the `decode' procedure to decode the message, and give the
result.
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
