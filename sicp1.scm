;; -*- mode: scheme; fill-column: 75; comment-column: 50; coding: utf-8; geiser-scheme-implementation: guile -*-

;; Chapter 1 of SICP
(use-modules (ice-9 format))
(use-modules (srfi srfi-41))


#| Utilities |#
(define inside-repl?
  ;; current-source-location is formatted in a line, column, filename alist
  ;; e.g ((line . INTEGER) (column . INTEGER) (filename . SYMBOL|FALSE))
  (eq? #f (assq-ref (current-source-location) 'filename)))

(define do-debug? #t)
(define (debug format-string . format-args)
  (if do-debug?
      (apply format `(#t
                      ,(string-append format-string "~&")
                      ,@format-args))))

(define (square x) (* x x))
(define (inc n) (+ n 1))
(define (average n m) (/ (+ n m) 2))
(define (double x) (+ x x))

(define (identity x) x)

(define tolerance 0.00001)

(define (fixed-point f first-guess)
  (define (close-enough? v1 v2)
    (< (abs (- v1 v2))
       tolerance))
  (define (try guess)
    (let ((next (f guess)))
      (if (close-enough? guess next)
          next
          (try next))))
  (try first-guess))

(define (average-damp f)
  (lambda (x)
    (average x (f x))))

(define dx 0.000001)
(define (deriv g)
  (lambda (x)
    (/ (- (g (+ x dx)) (g x))
       dx)))

(define (newton-transform g)
  (lambda (x)
    (- x (/ (g x)
            ((deriv g) x)))))

(define (newtons-method g guess)
  (fixed-point (newton-transform g)
               guess))


#| Exercise 1.1
Below is a sequence of expressions. What is the result printed by the
interpreter in response to each expression? Assume that the sequence is to be
evaluated in the order in which it is presented.

(Expressions Contained in Answer Section)
|#

#| Answer:

Respectively:

10
scheme@(guile-user)> 10

(+ 5 3 4)
scheme@(guile-user)> 12

(- 9 1)
scheme@(guile-user)> 8

(/ 6 2)
scheme@(guile-user)> 3

(+ (* 2 4) (- 4 6))
scheme@(guile-user)> 6

(define a 3)
(define b (+ a 1))
(+ a b (* a b))
scheme@(guile-user)> 19

(= a b)
scheme@(guile-user)> #f

(if (and (> b a) (< b (* a b)))
    b
    a)
scheme@(guile-user)> 4

(cond ((= a 4) 6)
      ((= b 4) (+ 6 7 a))
      (else 25))
scheme@(guile-user)> 16

(+ 2 (if (> b a) b a))
scheme@(guile-user)> 6

(* (cond ((> a b) a)
         ((< a b) b)
         (else -1))
   (+ a 1))
scheme@(guile-user)> 16
|#


#| Exercise 1.2
Translate the following expression into prefix form.

            5 + 4 + (2 - (3 - (6 + 4/5)))
            -----------------------------
                  3(6 - 2)(2 - 7)
|#

#| Answer:
(/ (+ (+ 5 4) (- 2 (- 3 (+ 6 (/ 4 5))))) (* 3 (- 6 2) (- 2 7)))
|#


#| Exercise 1.3
Define a procedure that takes three numbers as arguments and returns the sum of
the squares of the two larger numbers.
|#

(define (largest-squares x y z)
  (+
   (if (> x y) (square x) (square y))
   (if (> y z) (square y) (square z))))


#| Exercise 1.4
Observe that our model of evaluation allows for combinations whose operators are
compound expressions. Use this observation to describe the behavior of the
following procedure:

        (define (a-plus-abs-b a b)
          ((if (> b 0) + -) a b))
|#

#| Answer:
If b is greater than 0, add a to b.
Otherwise, subtract b from a
|#


#| Exercise 1.5
Ben Bitdiddle has invented a test to determine whether the interpreter he is
faced with is using applicative-order evaluation or normal-order evaluation. He
defines the following two procedures:

          (define (p) (p))

          (define (test x y)
            (if (= x 0)
                0
                y))

Then he evaluates the expression

          (test 0 (p))

What behavior will Ben observe with an interpreter that uses applicative-order
evaluation? What behavior will he observe with an interpreter that uses
normal-order evaluation? Explain your answer. (Assume that the evaluation rule
for the special form `if' is the same whether the interpreter is using normal or
applicative order: The predicate expression is evaluated first, and the result
determines whether to evaluate the consequent or the alternative expression.)
|#

#| Answer:
An applicative order evaluator would never terminate. The value of `p' is
expanded prior to the logic of `test' being applied.

Conversely, a normal-order evaluator would return 0, it never had the chance to
expand `p'
|#


#| Exercise 1.6
Alyssa P. Hacker doesn't see why `if' needs to be provided as a special form.
"Why can't I just define it as an ordinary procedure in terms of `cond'?" she
asks. Alyssa's friend Eva Lu Ator claims this can indeed be done, and she
defines a new version of `if':

         (define (new-if predicate then-clause else-clause)
           (cond (predicate then-clause)
                 (else else-clause)))

Eva demonstrates the program for Alyssa:

        (new-if (= 2 3) 0 5)
        5

        (new-if (= 1 1) 0 5)
        0

Delighted, Alyssa uses `new-if' to rewrite the square-root program:

        (define (sqrt-iter guess x)
          (new-if (good-enough? guess x)
                  guess
                  (sqrt-iter (improve guess x)
                            x)))

What happens when Alyssa attempts to use this to compute square
roots?  Explain.

|#

#| Answer:
Any function supplied to `new-if' will be applied, `sqrt-iter' will thus
infinitely loop.
|#


#| Exercise 1.7
The `good-enough?' test used in computing square roots will not be very
effective for finding the square roots of very small numbers. Also, in real
computers, arithmetic operations are almost always performed with limited
precision. This makes our test inadequate for very large numbers. Explain these
statements, with examples showing how the test fails for small and large
numbers.

An alternative strategy for implementing `good-enough?' is to watch how
`guess' changes from one iteration to the next and to stop when the change
is a very small fraction of the guess. Design a square-root procedure that
uses this kind of end test. Does this work better for small and large
numbers?

|#

(define (fix/sqrt-iter guess last-guess x)
  (let ([good-enough? (< (abs (- guess last-guess)) 0.001)]
        [next-guess (average guess (/ x guess))])
    (if good-enough? guess
        (fix/sqrt-iter next-guess guess x))))


#| Exercise 1.8
Newton's method for cube roots is based on the fact that if y is an
approximation to the cube root of x, then a better approximation is given
by the value

                x/y^2 + 2y
                ----------
                    3

Use this formula to implement a cube-root procedure analogous to the
square-root procedure. (In section 1.3.4 we will see how to implement
Newton's method in general as an abstraction of these square-root and
cube-root procedures.)

|#

(define (1.8/sqrt-iter guess last-guess x)
  (let ([good-enough? (< (abs (- guess last-guess)) 0.001)]
        [next-guess (/ (+ (/ x (square guess))
                       (* 2 guess))
                    3)])
    (if good-enough? guess
        (fix/sqrt-iter next-guess guess x))))


#| Exercise 1.9
Each of the following two procedures defines a method for adding two
positive integers in terms of the procedures `inc', which increments its
argument by 1, and `dec', which decrements its argument by 1.

          (define (+ a b)
            (if (= a 0)
              b
              (inc (+ (dec a) b))))

          (define (+ a b)
            (if (= a 0)
              b
             (+ (dec a) (inc b))))

Using the substitution model, illustrate the process generated by each
procedure in evaluating `(+ 4 5)'. Are these processes iterative or
recursive?

|#


#| Answer:

The first is recursive:

  scheme@(guile-user)> ,trace (+ 4 5)

  trace: |  (+ 4 5)
  trace: |  |  (+ 3 5)
  trace: |  |  |  (+ 2 5)
  trace: |  |  |  |  (+ 1 5)
  trace: |  |  |  |  |  (+ 0 5)
  trace: |  |  |  |  |  5
  trace: |  |  |  |  6
  trace: |  |  |  7
  trace: |  |  8
  trace: |  9

The second function is iterative

  scheme@(guile-user)> ,trace (pl 4 5)
  trace: |  (pl 4 5)
  trace: |  |  (dec 4)
  trace: |  |  3
  trace: |  |  (inc 5)
  trace: |  |  6
  trace: |  (pl 3 6)
  trace: |  |  (dec 3)
  trace: |  |  2
  trace: |  |  (inc 6)
  trace: |  |  7
  trace: |  (pl 2 7)
  trace: |  |  (dec 2)

  trace: |  |  1
  trace: |  |  (inc 7)
  trace: |  |  8
  trace: |  (pl 1 8)
  trace: |  |  (dec 1)
  trace: |  |  0
  trace: |  |  (inc 8)
  trace: |  |  9
  trace: |  (pl 0 9)
  trace: |  9

|#


#| Exercise 1.10
The following procedure computes a mathematical function called Ackermann's
function. |#

     (define (A x y)
       (cond ((= y 0) 0)
             ((= x 0) (* 2 y))
             ((= y 1) 2)
             (else (A (- x 1)
                      (A x (- y 1))))))

#| What are the values of the following expressions?

      (A 1 10)
      (A 2 4)
      (A 3 3)

Consider the following procedures, where A is the procedure defined above:

      (define (f n) (A 0 n))
      (define (g n) (A 1 n))
      (define (h n) (A 2 n))
      (define (k n) (* 5 n n))

Give concise mathematical definitions for the functions computed by the
procedures f, g, and h for positive integer values of n. For example, (k n)
computes 5n^2.

|#

#| Answer:

A trace of the first Ackermann function shown produces a long list of
recursive calls, which is only exaggerated as `x' increases.

  scheme@(guile-user)> ,trace (A 1 10)
  trace: |  (A 1 10)
  trace: |  |  (A 1 9)
  trace: |  |  |  (A 1 8)
  trace: |  |  |  |  (A 1 7)
  trace: |  |  |  |  |  (A 1 6)
  trace: |  |  |  |  |  |  (A 1 5)
  trace: |  |  |  |  |  |  |  (A 1 4)
  trace: |  |  |  |  |  |  |  |  (A 1 3)
  trace: |  |  |  |  |  |  |  |  |  (A 1 2)
  trace: |  |  |  |  |  |  |  |  |  |  (A 1 1)
  trace: |  |  |  |  |  |  |  |  |  |  2
  trace: |  |  |  |  |  |  |  |  |  (A 0 2)
  trace: |  |  |  |  |  |  |  |  |  4
  trace: |  |  |  |  |  |  |  |  (A 0 4)
  trace: |  |  |  |  |  |  |  |  8
  trace: |  |  |  |  |  |  |  (A 0 8)
  trace: |  |  |  |  |  |  |  16
  trace: |  |  |  |  |  |  (A 0 16)
  trace: |  |  |  |  |  |  32
  trace: |  |  |  |  |  (A 0 32)
  trace: |  |  |  |  |  64
  trace: |  |  |  |  (A 0 64)
  trace: |  |  |  |  128
  trace: |  |  |  (A 0 128)
  trace: |  |  |  256
  trace: |  |  (A 0 256)
  trace: |  |  512
  trace: |  (A 0 512)
  trace: |  1024
  scheme@(guile-user)> (A 2 4)
  $2 = 65536
  scheme@(guile-user)> (A 3 3)
  $3 = 65536


The functions described can be simplified as follows:

  (define (f n) (A 0 n))
  →  2n

  (define (g n) (A 1 n))
  →  n²

  (define (h n) (A 2 n))
  →  2↑n

|#


#| Exercise 1.11
A function f is defined by the rule that

    f(n) = n if n < 3

and

    f(n) = f(n - 1) + 2f(n - 2) + 3f(n - 3) if n >= 3.

Write a procedure that computes f by means of a recursive process.
Write a procedure that computes f by means of an iterative process.
|#

(define (rule1.11/recursive n)
  (if (< n 3) n
      (+ (rule1.11/recursive (- n 1))
         (* 2 (rule1.11/recursive (- n 2)))
         (* 3 (rule1.11/recursive (- n 3))))))

(define (rule1.11/iterative n)
  (define (driver count a b c)
    (if (= count n) c
        (driver (+ count 1)
                       (+ a (* 2 b) (* 3 c))
                       a
                       b)))
  (driver 0 2 1 0))


#| Exercise 1.12
The following pattern of numbers is called "Pascal's triangle".

                                1
                              1   1
                            1   2   1
                          1   3   3   1
                        1   4   6   4   1

The numbers at the edge of the triangle are all 1, and each number inside
the triangle is the sum of the two numbers above it. Write a procedure that
computes elements of Pascal's triangle by means of a recursive process.
|#

(define (pascals-triangle depth)
  ;; `build-entry' doesn't memoize the finding of each number. You could do
  ;; so either here or with more changes to `build-row'.
  (define (build-entry rows col)
    (cond
     [(and (= rows 0) (= col 0)) 1]
     [(or (< col 0) (< rows col)) 0]
     [else (+ (build-entry (- rows 1) (- col 1))
              (build-entry (- rows 1) col))]))

  (define (build-row ctr length)
    (if (= ctr (1+ length)) '()
        (cons (build-entry length ctr) (build-row (+ ctr 1) length))))

  (define (build n)
    (if (= n depth) '()
        (cons (build-row 0 n) (build (1+ n)))))

  (build 0))


#| Exercise 1.13
Prove that Fib(n) is the closest integer to φⁿ/√5, where φ = (1 + √5)/2.
Hint: Let ψ = (1−√5)/2. Use induction and the definition of the Fibonacci
numbers (see section *Note 1.2.2) to prove that Fib(n) = (φⁿ - ψⁿ) / √5
|#


#| Exercise 1.14
Draw the tree illustrating the process generated by the `count-change'
procedure of section *Note 1.2.2 in making change for 11 cents. What are
the orders of growth of the space and number of steps used by this process
as the amount to be changed increases?
|#

#| Answer:
trace: (count-change 11)
trace: (cc 11 5)
trace: |  (cc 11 4)
trace: |  |  (cc 11 3)
trace: |  |  |  (cc 11 2)
trace: |  |  |  |  (cc 11 1)
trace: |  |  |  |  |  (cc 11 0)
trace: |  |  |  |  |  0
trace: |  |  |  |  |  (first-denomination 1)
trace: |  |  |  |  |  1
trace: |  |  |  |  |  (cc 10 1)
trace: |  |  |  |  |  |  (cc 10 0)
trace: |  |  |  |  |  |  0
trace: |  |  |  |  |  |  (first-denomination 1)
trace: |  |  |  |  |  |  1
trace: |  |  |  |  |  |  (cc 9 1)
trace: |  |  |  |  |  |  |  (cc 9 0)
trace: |  |  |  |  |  |  |  0
trace: |  |  |  |  |  |  |  (first-denomination 1)
trace: |  |  |  |  |  |  |  1
trace: |  |  |  |  |  |  |  (cc 8 1)
trace: |  |  |  |  |  |  |  |  (cc 8 0)
trace: |  |  |  |  |  |  |  |  0
trace: |  |  |  |  |  |  |  |  (first-denomination 1)
trace: |  |  |  |  |  |  |  |  1
trace: |  |  |  |  |  |  |  |  (cc 7 1)
trace: |  |  |  |  |  |  |  |  |  (cc 7 0)
trace: |  |  |  |  |  |  |  |  |  0
trace: |  |  |  |  |  |  |  |  |  (first-denomination 1)
trace: |  |  |  |  |  |  |  |  |  1
trace: |  |  |  |  |  |  |  |  |  (cc 6 1)
trace: |  |  |  |  |  |  |  |  |  |  (cc 6 0)
trace: |  |  |  |  |  |  |  |  |  |  0
trace: |  |  |  |  |  |  |  |  |  |  (first-denomination 1)
trace: |  |  |  |  |  |  |  |  |  |  1
trace: |  |  |  |  |  |  |  |  |  |  (cc 5 1)
trace: |  |  |  |  |  |  |  |  |  |  |  (cc 5 0)
trace: |  |  |  |  |  |  |  |  |  |  |  0
trace: |  |  |  |  |  |  |  |  |  |  |  (first-denomination 1)
trace: |  |  |  |  |  |  |  |  |  |  |  1
trace: |  |  |  |  |  |  |  |  |  |  |  (cc 4 1)
trace: |  |  |  |  |  |  |  |  |  |  |  |  (cc 4 0)
trace: |  |  |  |  |  |  |  |  |  |  |  |  0
trace: |  |  |  |  |  |  |  |  |  |  |  |  (first-denomination 1)
trace: |  |  |  |  |  |  |  |  |  |  |  |  1
trace: |  |  |  |  |  |  |  |  |  |  |  |  (cc 3 1)
trace: |  |  |  |  |  |  |  |  |  |  |  |  |  (cc 3 0)
trace: |  |  |  |  |  |  |  |  |  |  |  |  |  0
trace: |  |  |  |  |  |  |  |  |  |  |  |  |  (first-denomination 1)
trace: |  |  |  |  |  |  |  |  |  |  |  |  |  1
trace: |  |  |  |  |  |  |  |  |  |  |  |  |  (cc 2 1)
trace: |  |  |  |  |  |  |  |  |  |  |  |  |  15> (cc 2 0)
trace: |  |  |  |  |  |  |  |  |  |  |  |  |  15< 0
trace: |  |  |  |  |  |  |  |  |  |  |  |  |  15> (first-denomination 1)
trace: |  |  |  |  |  |  |  |  |  |  |  |  |  15< 1
trace: |  |  |  |  |  |  |  |  |  |  |  |  |  15> (cc 1 1)
trace: |  |  |  |  |  |  |  |  |  |  |  |  |  16> (cc 1 0)
trace: |  |  |  |  |  |  |  |  |  |  |  |  |  16< 0
trace: |  |  |  |  |  |  |  |  |  |  |  |  |  16> (first-denomination 1)
trace: |  |  |  |  |  |  |  |  |  |  |  |  |  16< 1
trace: |  |  |  |  |  |  |  |  |  |  |  |  |  16> (cc 0 1)
trace: |  |  |  |  |  |  |  |  |  |  |  |  |  16< 1
trace: |  |  |  |  |  |  |  |  |  |  |  |  |  15< 1
trace: |  |  |  |  |  |  |  |  |  |  |  |  |  1
trace: |  |  |  |  |  |  |  |  |  |  |  |  1
trace: |  |  |  |  |  |  |  |  |  |  |  1
trace: |  |  |  |  |  |  |  |  |  |  1
trace: |  |  |  |  |  |  |  |  |  1
trace: |  |  |  |  |  |  |  |  1
trace: |  |  |  |  |  |  |  1
trace: |  |  |  |  |  |  1
trace: |  |  |  |  |  1
trace: |  |  |  |  1
trace: |  |  |  |  (first-denomination 2)
trace: |  |  |  |  5
trace: |  |  |  |  (cc 6 2)
trace: |  |  |  |  |  (cc 6 1)
trace: |  |  |  |  |  |  (cc 6 0)
trace: |  |  |  |  |  |  0
trace: |  |  |  |  |  |  (first-denomination 1)
trace: |  |  |  |  |  |  1
trace: |  |  |  |  |  |  (cc 5 1)
trace: |  |  |  |  |  |  |  (cc 5 0)
trace: |  |  |  |  |  |  |  0
trace: |  |  |  |  |  |  |  (first-denomination 1)
trace: |  |  |  |  |  |  |  1
trace: |  |  |  |  |  |  |  (cc 4 1)
trace: |  |  |  |  |  |  |  |  (cc 4 0)
trace: |  |  |  |  |  |  |  |  0
trace: |  |  |  |  |  |  |  |  (first-denomination 1)
trace: |  |  |  |  |  |  |  |  1
trace: |  |  |  |  |  |  |  |  (cc 3 1)
trace: |  |  |  |  |  |  |  |  |  (cc 3 0)
trace: |  |  |  |  |  |  |  |  |  0
trace: |  |  |  |  |  |  |  |  |  (first-denomination 1)
trace: |  |  |  |  |  |  |  |  |  1
trace: |  |  |  |  |  |  |  |  |  (cc 2 1)
trace: |  |  |  |  |  |  |  |  |  |  (cc 2 0)
trace: |  |  |  |  |  |  |  |  |  |  0
trace: |  |  |  |  |  |  |  |  |  |  (first-denomination 1)
trace: |  |  |  |  |  |  |  |  |  |  1
trace: |  |  |  |  |  |  |  |  |  |  (cc 1 1)
trace: |  |  |  |  |  |  |  |  |  |  |  (cc 1 0)
trace: |  |  |  |  |  |  |  |  |  |  |  0
trace: |  |  |  |  |  |  |  |  |  |  |  (first-denomination 1)
trace: |  |  |  |  |  |  |  |  |  |  |  1
trace: |  |  |  |  |  |  |  |  |  |  |  (cc 0 1)
trace: |  |  |  |  |  |  |  |  |  |  |  1
trace: |  |  |  |  |  |  |  |  |  |  1
trace: |  |  |  |  |  |  |  |  |  1
trace: |  |  |  |  |  |  |  |  1
trace: |  |  |  |  |  |  |  1
trace: |  |  |  |  |  |  1
trace: |  |  |  |  |  1
trace: |  |  |  |  |  (first-denomination 2)
trace: |  |  |  |  |  5
trace: |  |  |  |  |  (cc 1 2)
trace: |  |  |  |  |  |  (cc 1 1)
trace: |  |  |  |  |  |  |  (cc 1 0)
trace: |  |  |  |  |  |  |  0
trace: |  |  |  |  |  |  |  (first-denomination 1)
trace: |  |  |  |  |  |  |  1
trace: |  |  |  |  |  |  |  (cc 0 1)
trace: |  |  |  |  |  |  |  1
trace: |  |  |  |  |  |  1
trace: |  |  |  |  |  |  (first-denomination 2)
trace: |  |  |  |  |  |  5
trace: |  |  |  |  |  |  (cc -4 2)
trace: |  |  |  |  |  |  0
trace: |  |  |  |  |  1
trace: |  |  |  |  2
trace: |  |  |  3
trace: |  |  |  (first-denomination 3)
trace: |  |  |  10
trace: |  |  |  (cc 1 3)
trace: |  |  |  |  (cc 1 2)
trace: |  |  |  |  |  (cc 1 1)
trace: |  |  |  |  |  |  (cc 1 0)
trace: |  |  |  |  |  |  0
trace: |  |  |  |  |  |  (first-denomination 1)
trace: |  |  |  |  |  |  1
trace: |  |  |  |  |  |  (cc 0 1)
trace: |  |  |  |  |  |  1
trace: |  |  |  |  |  1
trace: |  |  |  |  |  (first-denomination 2)
trace: |  |  |  |  |  5
trace: |  |  |  |  |  (cc -4 2)
trace: |  |  |  |  |  0
trace: |  |  |  |  1
trace: |  |  |  |  (first-denomination 3)
trace: |  |  |  |  10
trace: |  |  |  |  (cc -9 3)
trace: |  |  |  |  0
trace: |  |  |  1
trace: |  |  4
trace: |  |  (first-denomination 4)
trace: |  |  25
trace: |  |  (cc -14 4)
trace: |  |  0
trace: |  4
trace: |  (first-denomination 5)
trace: |  50
trace: |  (cc -39 5)
trace: |  0
trace: 4
|#


#| Exercise 1.15
The sine of an angle (specified in radians) can be computed by making use
of the approximation `sin' xapprox x if x is sufficiently small, and the
trigonometric identity

                         x             x
          sin x = 3 sin --- - 4 sin^3 ---
                         3             3

to reduce the size of the argument of `sin'. (For purposes of this
exercise an angle is considered "sufficiently small" if its magnitude is
not greater than 0.1 radians.) These ideas are incorporated in the
following procedures:

          (define (cube x) (* x x x))

          (define (p x) (- (* 3 x) (* 4 (cube x))))

          (define (sine angle)
             (if (not (> (abs angle) 0.1))
                 angle
                 (p (sine (/ angle 3.0)))))

a. How many times is the procedure `p' applied when `(sine 12.15)' is
evaluated?

b. What is the order of growth in space and number of steps (as a function
of a) used by the process generated by the `sine' procedure when `(sine a)'
is evaluated?
|#

#| Answer:
a. The procedure is evaluated 5 times
b. The order of growth is O(log(n))
|#


#| Exercise 1.16
Design a procedure that evolves an iterative exponentiation process that
uses successive squaring and uses a logarithmic number of steps, as does
`fast-expt'.

(Hint: Using the observation that (bⁿ/²)²= (b²)ⁿ/², keep, along with the
exponent `n' and the base `b', an additional state variable `a', and define
the state transformation in such a way that the product abⁿ is unchanged
from state to state. At the beginning of the process a is taken to be 1,
and the answer is given by the value of `a' at the end of the process. In
general, the technique of defining an "invariant quantity" that remains
unchanged from state to state is a powerful way to think about the design
of iterative algorithms.)
|#

(define (zv/expt-iter b n a)
  (cond
   [(= n 0) a]
   [(even? n) (zv/expt-iter (* b b) (/ n 2) a)]
   [else      (zv/expt-iter  b (- n 1) (* a b))]))


#| Exercise 1.17
The exponentiation algorithms in this section are based on performing
exponentiation by means of repeated multiplication. In a similar way, one
can perform integer multiplication by means of repeated addition. The
following multiplication procedure (in which it is assumed that our
language can only add, not multiply) is analogous to the `expt' procedure:

          (define (* a b)
            (if (= b 0)
              0
              (+ a (* a (- b 1)))))

This algorithm takes a number of steps that is linear in `b'. Now suppose
we include, together with addition, operations `double', which doubles an
integer, and `halve', which divides an (even) integer by 2. Using these,
design a multiplication procedure analogous to `fast-expt' that uses a
logarithmic number of steps.
|#

(define (1.17/fast-* a b)
  (define (double x) (+ x x))
  (define (halve x) (/ x 2))
  (cond ((= b 0) 0)
        ((even? b) (double (* a (halve b))))
        (else (+ a (* a (- b 1))))))


#| TODO Exercise 1.18
Using the results of *Note Exercise 1.16 and *Note Exercise 1.17, devise a
procedure that generates an iterative process for multiplying two integers
in terms of adding, doubling, and halving and uses a logarithmic number of
steps.
|#


#| Exercise 1.19
There is a clever algorithm for computing the Fibonacci numbers in a
logarithmic number of steps. Recall the transformation of the state
variables a and b in the fib-iter process of 1.2.2: a ← a + b and b ← a.
Call this transformation T, and observe that applying T over and over again
n times, starting with 1 and 0, produces the pair Fib(n + 1) and Fib(n) .
In other words, the Fibonacci numbers are produced by applying T n, the
n-th power of the transformation T, starting with the pair (1, 0). Now
consider T to be the special case of p = 0 and q = 1 in a family of
transformations T_pq , where T_pq transforms the pair(a, b) according to a
← bq + aq + ap and b ← bp + aq .

Show that if we apply such a transformation T_pq twice, the effect is the
same as using a single transformation T_p′q′ of the same form, and compute
p′ and q′ in terms of p and q .

This gives us an explicit way to square these transformations, and thus we
can compute T n using successive squaring, as in the fast-expt procedure.

Put this all together to complete the following procedure, which runs in a
logarithmic number of steps:
|#

(define (1.19/fib n)
  (1.19/fib-iter 1 0 0 1 n))

(define (1.19/fib-iter a b p q count)
  (cond ((= count 0) b)
        ((even? count)
         (1.19/fib-iter a
                   b
                   (+ (square p) (square q)) ; compute p'
                   (+ (* 2 p q) (square q))  ; compute q'
                   (/ count 2)))
        (else (1.19/fib-iter (+ (* b q) (* a q) (* a p))
                        (+ (* b p) (* a q))
                        p
                        q
                        (- count 1)))))
;; TODO XXX write test


#| Exercise 1.20
The process that a procedure generates is of course dependent on the rules
used by the interpreter. As an example, consider the iterative `gcd'
procedure given above. Suppose we were to interpret this procedure using
normal-order evaluation, as discussed in section *Note 1-1-5. (The
normal-order-evaluation rule for `if' is described in *Note Exercise 1-5)
Using the substitution method (for normal order), illustrate the process
generated in evaluating `(gcd 206 40)' and indicate the `remainder'
operations that are actually performed. How many `remainder' operations are
actually performed in the normal-order evaluation of `(gcd 206 40)'? In the
applicative-order evaluation?
|#

#| Answer
Performs 18 `remainder' operations
|#

#| Exercise 1.21
Use the smallest-divisor procedure to find the smallest divisor of each of
the following numbers: 199, 1999, 19999.
|#
(define (divides? a b)
  (= (remainder b a) 0))

(define (find-divisor n test-divisor)
  (cond ((> (square test-divisor) n) n)
        ((divides? test-divisor n) test-divisor)
        (else (find-divisor n (+ test-divisor 1)))))

(define (smallest-divisor n)
  (find-divisor n 2))

;; TODO XXX write test
;; (format #f "~a" (for-each smallest-divisor '(199 1999 1999)))


#| Exercise 1.22
Most Lisp implementations include a primitive called `runtime' that returns
an integer that specifies the amount of time the system has been running
(measured, for example, in microseconds). The following `timed-prime-test'
procedure, when called with an integer n, prints n and checks to see if n
is prime. If n is prime, the procedure prints three asterisks followed by
the amount of time used in performing the test.
|#
          (define (timed-prime-test n)
            (newline)
            (display n)
            (start-prime-test n (current-time)))

          (define (start-prime-test n start-time)
            (if (prime? n)
                (report-prime (- (current-time) start-time))))

          (define (report-prime elapsed-time)
            (display " *** ")
            (display elapsed-time)
            #t)

#|
Using this procedure, write a procedure `search-for-primes' that
checks the primality of consecutive odd integers in a specified range. Use
your procedure to find the three smallest primes larger than 1000; larger
than 10,000; larger than 100,000; larger than 1,000,000. Note the time
needed to test each prime. Since the testing algorithm has order of growth
of [theta](_[sqrt]_(n)), you should expect that testing for primes around
10,000 should take about _[sqrt]_(10) times as long as testing for primes
around 1000. Do your timing data bear this out? How well do the data for
100,000 and 1,000,000 support the _[sqrt]_(n) prediction? Is your result
compatible with the notion that programs on your machine run in time
proportional to the number of steps required for the computation?
|#
(define (prime? n)
  (= n (smallest-divisor n)))

(define (expmod base exp m)
  (cond ((= exp 0) 1)
        ((even? exp)
         (remainder
          (square (expmod base (/ exp 2) m))
          m))
        (else
         (remainder
          (* base (expmod base (- exp 1) m))
          m))))

(define (search-for-primes start)
  (define (is-prime? n)
    (cond
     [(even? n) #f]
     [(< n 0) #f]
     [(timed-prime-test n) #t]
     [else (is-prime? (- n 2))]))

  (define (driver n primes count)
    (cond
     [(even? n) (driver (+ n 1) primes count)]
     [(= count 3) primes]
     [(is-prime? n) (driver (+ n 2) (cons n primes) (+ count 1))]
     [else (driver (+ n 2) primes count)]))

  (driver start '() 0))
;;; TODO XXX write test


#| Exercise 1.23
The `smallest-divisor' procedure shown at the start of this section does
lots of needless testing: After it checks to see if the number is divisible
by 2 there is no point in checking to see if it is divisible by any larger
even numbers. This suggests that the values used for `test-divisor' should
not be 2, 3, 4, 5, 6, ..., but rather 2, 3, 5, 7, 9, .... To implement this
change, define a procedure `next' that returns 3 if its input is equal to 2
and otherwise returns its input plus 2. Modify the `smallest-divisor'
procedure to use `(next test-divisor)' instead of `(+ test-divisor 1)'.
With `timed-prime-test' incorporating this modified version of
`smallest-divisor', run the test for each of the 12 primes found Note in 1.22
Since this modification halves the number of test steps, you should expect
it to run about twice as fast. Is this expectation confirmed? If not, what
is the observed ratio of the speeds of the two algorithms, and how do you
explain the fact that it is different from 2?
|#

(define (1.23/next n) (if (= n 2) 3 (+ n 2)))


#| TODO Exercise 1.24
Modify the `timed-prime-test' procedure of *Note Exercise 1-22 to use
`fast-prime?' (the Fermat method), and test each of the 12 primes you found
in that exercise. Since the Fermat test has [theta](`log' n) growth, how
would you expect the time to test primes near 1,000,000 to compare with the
time needed to test primes near 1000? Do your data bear this out? Can you
explain any discrepancy you find?
|#


#| Exercise 1.25
Alyssa P. Hacker complains that we went to a lot of extra work in writing
`expmod'. After all, she says, since we already know how to compute
exponentials, we could have simply written

          (define (expmod base exp m)
            (remainder (fast-expt base exp) m))

Is she correct? Would this procedure serve as well for our fast prime
tester? Explain. |#

#| Answer:
Depending on the behavior of large values of `base' and `exp' combined with
the system's handling of large numbers, it is either a middling gain or an
enormously slower operation. |#


#| Exercise 1.26
Louis Reasoner is having great difficulty doing *Note Exercise 1.24. His
`fast-prime?' test seems to run more slowly than his `prime?' test. Louis
calls his friend Eva Lu Ator over to help. When they examine Louis's code,
they find that he has rewritten the `expmod' procedure to use an explicit
multiplication, rather than calling `square':

          (define (expmod base exp m)
            (cond ((= exp 0) 1)
                  ((even? exp)
                   (remainder (* (expmod base (/ exp 2) m)
                                 (expmod base (/ exp 2) m))
                              m))
                  (else
                   (remainder (* base (expmod base (- exp 1) m))
                              m))))

"I don't see what difference that could make," says Louis. "I do."
says Eva. "By writing the procedure like that, you have transformed the
[theta](`log' n) process into a [theta](n) process." Explain. |#

#| Answer:
Assuming the computer doesn't perform any sort of sophisticated
memoization, effectively each step is performing twice as much work for n
steps, e.g n^2, trimming the speed of the original implementation down to
[theta](n). |#


#| TODO Exercise 1.27
Demonstrate that the Carmichael numbers listed in *Note Footnote 1.47
really do fool the Fermat test. That is, write a procedure that takes an
integer n and tests whether a^n is congruent to a modulo n for every a<n,
and try your procedure on the given Carmichael numbers. |#


#| Exercise 1.28
One variant of the Fermat test that cannot be fooled is called the
"Miller-Rabin test" (Miller 1976; Rabin 1980). This starts from an
alternate form of Fermat's Little Theorem, which states that if n is a
prime number and a is any positive integer less than n, then a raised to
the (n - 1)st power is congruent to 1 modulo n. To test the primality of a
number n by the Miller-Rabin test, we pick a random number a<n and raise a
to the (n - 1)st power modulo n using the `expmod' procedure. However,
whenever we perform the squaring step in `expmod', we check to see if we
have discovered a "nontrivial square root of 1 modulo n," that is, a number
not equal to 1 or n - 1 whose square is equal to 1 modulo n. It is possible
to prove that if such a nontrivial square root of 1 exists, then n is not
prime. It is also possible to prove that if n is an odd number that is not
prime, then, for at least half the numbers a<n, computing a^(n-1) in this
way will reveal a nontrivial square root of 1 modulo n. (This is why the
Miller-Rabin test cannot be fooled.) Modify the `expmod' procedure to
signal if it discovers a nontrivial square root of 1, and use this to
implement the Miller-Rabin test with a procedure analogous to
`fermat-test'. Check your procedure by testing various known primes and
non-primes. Hint: One convenient way to make `expmod' signal is to have it
return 0. |#


#| 1.29
Simpson’s Rule is a more accurate method of numerical integration than the
method illustrated above. Using Simpson’s Rule, the integral of a function
f between a and b is approximated as

    h/3 ⋅ (y₀ + 4y₁ + 2y₂ + 4y₃ + 2y₄ + ⋯ + 2y₍ₙ₋₂₎ + 4y₍ₙ₋₁₎ + yₙ)

where h = (b − a)/n, for some even integer n , and yₖ = f(a + kh).
(Increasing n increases the accuracy of the approximation.) Define a
procedure that takes as arguments f, a, b , and n and returns the value
of the integral, computed using Simpson’s Rule. Use your procedure to
integrate cube between 0 and 1 (with n = 100 and n = 1000 ), and compare
the results to those of the integral procedure shown above. |#

(define (sum term a next b)
  (if (> a b)
      0
      (+ (term a)
         (sum term (next a) next b))))

(define (sum-integers a b) (sum identity a inc b))

(define (integral f a b dx)
  (define (add-dx x) (+ x dx))
  (* (sum f (+ a (/ dx 2.0)) add-dx b)
     dx))

(define (simpsons-rule-solver f a b n)
  (let* ([h (/ (- b a) n)]
         ;; compute yₖ
         [fy (λ (k)
               (* (if (even? k) 4 2)
                  (f (+ a (* k h)))))])

    (* (/ h 3)
       (+ (f a) (sum fy 0 inc n) (f (+ a (* n h)))))))


#| Exercise 1.30
The sum procedure above generates a linear recursion. The procedure can be
rewritten so that the sum is performed iteratively. |#

(define (1.30/sum term a next b)
  (define (iter a result)
    (if (> a b)
        result
        (iter (next a) (+ (term a) result))))

  (iter a 0))


#| Exercise 1.31
1. The `sum' procedure is only the simplest of a vast number of similar
abstractions that can be captured as higher-order procedures. Write an
analogous procedure called product that returns the product of the values
of a function at points over a given range. Show how to define factorial in
terms of product. Also use product to compute approximations to π using the
formula:

    π/4 = 2/3 ⋅ 4/3 ⋅ 4/5 ⋅ 6/5 ⋅ 6/7 ⋅ 8/7

2. If your product procedure generates a recursive process, write one that
generates an iterative process. If it generates an iterative process, write
one that generates a recursive process. |#

(define (recursive-product term a next b)
  (if (> a b) a)
  (* (term a)
     (recursive-product term (next a) next b)))

(define (iterative-product term a next b)
  (define (iter a result)
    (if (> a b)
        result
        (iter (next a) (* (term a) result))))

  (iter a 0))

(define (1.31/factorial n)
  (if (zero? n) 1
      (iterative-product identity 1 inc n)))

(define (1.31/pi-approximate n)
  (define (fnth nth)
    (if (even? nth)
        (/ (double nth) (inc (double nth)))
        (/ (inc (double nth)) (double nth))))

  (* 4.0 (iterative-product fnth 0 inc n)))


#| Exercise 1.32
1. Show that sum and product (Exercise 1.31) are both special cases of a still
more general notion called accumulate that combines a collection of terms,
using some general accumulation function:

      (accumulate
          combiner null-value term a next b)

Accumulate takes as arguments the same term and range specifications as sum
and product, together with a combiner procedure (of two arguments) that
specifies how the current term is to be combined with the accumulation of
the preceding terms and a null-value that specifies what base value to use
when the terms run out. Write accumulate and show how sum and product can
both be defined as simple calls to accumulate.

2. If your accumulate procedure generates a recursive process, write one
that generates an iterative process. If it generates an iterative process,
write one that generates a recursive process. |#

(define (1.32/recursive-accumulate combiner null term a next b)
  (if (> a b) a
      (combiner (term a)
                (1.32/recursive-accumulate combiner null term (next a) next b))))

(define (1.32/iterative-accumulate combiner null term a next b)
  (define (fold-left n acc)
    (if (> n b) acc
        (fold-left (next n) (combiner (term n) acc))))
  (fold-left a null))

;; XXX: add to test
;; (1.32/iterative-accumulate * 1 identity 1 inc 5) => 120


#| Exercise 1.33
You can obtain an even more general version of accumulate (Exercise 1.32)
by introducing the notion of a filter on the terms to be combined. That is,
combine only those terms derived from values in the range that satisfy a
specified condition. The resulting `filtered-accumulate' abstraction takes
the same arguments as `accumulate', together with an additional predicate of
one argument that specifies the filter. Write `filtered-accumulate' as a
procedure. Show how to express the following using `filtered-accumulate':

1. the sum of the squares of the prime numbers in the interval a to b
(assuming that you have a prime? predicate already written)

2. the product of all the positive integers less than n that are relatively
prime to n (i.e., all positive integers i < n such that GCD (i, n) = 1). |#

(define (1.33/filtered-accumulate combiner null term a next b filter)
  (if (> a b) null
      (if (filter a)
          (combiner (term a)
                    (1.33/filtered-accumulate combiner null term (next a) next b filter))
          (1.33/filtered-accumulate combiner null term (next a) next b filter))))

(define (1.33/sum-of-prime-squares a b)
  (1.33/filtered-accumulate + 0 square a inc b prime?))

(define (1.33/coprimes n)
  (1.33/filtered-accumulate * 1 identity 1 inc n (λ (i) (= 1 (gcd i n)))))


#| Exercise 1.34
Suppose we define the procedure

        (define (f g) (g 2))

Then we have

        (f square)
        4

        (f (lambda (z) (* z (+ z 1))))
        6

What happens if we (perversely) ask the interpreter to evaluate the
combination (f f)?

Explain. |#


#| Answer:

Infinite Loop |#


#| Exercise 1.35
Show that the golden ratio φ (1.2.2) is a fixed point of the transformation
x↦1+1/x, and use this fact to compute φ by means of the fixed-point
procedure. |#

(define (1.35/find-golden-ratio)
  (fixed-point (λ (n) (+ 1 (/ 1 n))) 1))


#| Exercise 1.36
Modify fixed-point so that it prints the sequence of approximations it
generates, using the newline and display primitives shown in Exercise 1.22.
Then find a solution to xⁿ=1000 by finding a fixed point of
x↦log(1000)/log(x). (Use Scheme’s primitive log procedure, which computes
natural logarithms.) Compare the number of steps this takes with and
without average damping. (Note that you cannot start fixed-point with a
guess of 1, as this would cause division by log(1)=0.)
|#


#| Exercise 1.37
a. An infinite "continued fraction" is an expression of the form

                  N_1
        f = ---------------------
                      N_2
            D_1 + ---------------
                          N_3
                  D_2 + ---------
                        D_3 + ...

  As an example, one can show that the infinite continued
  fraction expansion with the Nᵢ and the Dᵢ all equal to 1
  produces 1/φ, where φ is the golden ratio (described
  in section *Note 1.2.2).  One way to approximate an
  infinite continued fraction is to truncate the expansion
  after a given number of terms.  Such a truncation--a
  so-called finite continued fraction "k-term finite continued
  fraction"--has the form

              N_1
        -----------------
                  N_2
        D_1 + -----------
              ...    N_K
                  + -----
                    D_K

  Suppose that `n' and `d' are procedures of one argument (the
  term index i) that return the Nᵢ and Dᵢ of the terms of the
  continued fraction.  Define a procedure `cont-frac' such that
  evaluating `(cont-frac n d k)' computes the value of the
  k-term finite continued fraction.  Check your procedure by
  approximating 1/φ using

        (cont-frac (lambda (i) 1.0)
                  (lambda (i) 1.0)
                  k)

  for successive values of `k'.  How large must you make `k' in
  order to get an approximation that is accurate to 4 decimal
  places?

b. If your `cont-frac' procedure generates a recursive process,
  write one that generates an iterative process.  If it
  generates an iterative process, write one that generates a
  recursive process. |#

#| Answer:
`k' must be 10 or higher in order to print 1/phi correctly. |#

(define (1.37/cont-frac-recursive n d kth)
  (define (nth-continuation nth)
    (if (> nth kth) (d nth)
        (/ (n nth)
           (+ (d nth) (nth-continuation (inc nth))))))
  (nth-continuation 1))

(define (1.37/cont-frac-iter n d kth)
  (define (nth-continuation nth acc)
    (if (> nth kth) acc
        (nth-continuation (inc nth)
                          (/ (n nth) (+ (d nth) acc)))))
  (nth-continuation 1 0))

(define cont-frac 1.37/cont-frac-iter)

#| Exercise 1.38
In 1737, the Swiss mathematician Leonhard Euler published a memoir `De
Fractionibus Continuis', which included a continued fraction expansion for
e - 2, where e is the base of the natural logarithms. In this fraction, the
nᵢ are all 1, and the Dᵢ are successively 1, 2, 1, 1, 4, 1, 1, 6, 1, 1,
8, .... Write a program that uses your `cont-frac' procedure from Exercise
1.37 to approximate e, based on Euler's expansion. |#

(define (e-2 k)
  (cont-frac
   (λ (i) 1.0)
   (λ (n) (if (= 0 (modulo (+ n 1) 3))
              (* 2 (/ (+ n 1) 3))
              1))
   k))


#| Exercise 1.39
A continued fraction representation of the
tangent function was published in 1770 by the German mathematician
J.H. Lambert:

x
tan x = ---------------
x^2
1 - -----------
x^2
3 - -------
5  - ...

where x is in radians.  Define a procedure `(tan-cf x k)' that
computes an approximation to the tangent function based on
Lambert's formula.  `K' specifies the number of terms to compute,
as in *Note Exercise 1.37 |#

(define (1.39/tan-cf x k)
  (cont-frac (λ (i) (if (= i 1) x (* -1.0 (* x x))))
             (λ (i) (- (* i 2) 1.0))
             k))


#| Exercise 1.40
Define a procedure cubic that can be used together with the newtons-method
procedure in expressions of the form

    (newtons-method (cubic a b c) 1)

to approximate zeros of the cubic x³+ax²+bx+c. |#

(define (cubic a b c)
  (λ (x)
    (+ (* x x x)
       (* a (* x x))
       (* b x)
       c)))


#| Exercise 1.41
Define a procedure double that takes a procedure of one argument as
argument and returns a procedure that applies the original procedure twice.
For example, if inc is a procedure that adds 1 to its argument, then
(double inc) should be a procedure that adds 2. What value is returned by

    (((double (double double)) inc) 5)

? |#

(define (1.41/double fn) (λ (n) (fn (fn n))))


#| Exercise 1.42
Let f and g be two one-argument functions. The composition f after g is
defined to be the function x↦f(g(x)). Define a procedure compose that
implements composition. For example, if inc is a procedure that adds 1 to
its argument,

    ((compose square inc) 6)
    49

|#

(define (1.42/compose f g) (λ (n) (f (g n))))


#| Exercise 1.43
If f is a numerical function and n is a positive integer, then we can form
the nth repeated application of f, which is defined to be the function
whose value at x is f(f(…(f(x))…)). For example, if f is the function
x↦x+1, then the nth repeated application of f is the function x↦x+n. If f
is the operation of squaring a number, then the nth repeated application of
f is the function that raises its argument to the 2n-th power. Write a
procedure that takes as inputs a procedure that computes f and a positive
integer n and returns the procedure that computes the nth repeated
application of f. Your procedure should be able to be used as follows:

    ((repeated square 2) 5)
    625

Hint: You may find it convenient to use compose from Exercise 1.42. |#

(define (1.43/repeated-apply fn times)
  (if (= times 1) (λ (n) (fn n))
      (λ (n)
        (fn
         ((1.43/repeated-apply fn (- times 1)) n)))))


#| Exercise 1.44
The idea of smoothing a function is an important concept in signal
processing. If f is a function and dx is some small number, then the
smoothed version of f is the function whose value at a point x is the
average of f(x−dx), f(x), and f(x+dx). Write a procedure smooth that takes
as input a procedure that computes f and returns a procedure that computes
the smoothed f. It is sometimes valuable to repeatedly smooth a function
(that is, smooth the smoothed function, and so on) to obtain the n-fold
smoothed function. Show how to generate the n-fold smoothed function of any
given function using smooth and repeated from Exercise 1.43. |#

(define (1.44/smooth f)
  (λ (x)
    (/ (+ (f (- x dx))
          (f x)
          (f (+ x dx)))
       3)))

