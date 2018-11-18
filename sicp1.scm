;; -*- mode: scheme; fill-column: 75; comment-column: 50; coding: utf-8; geiser-scheme-implementation: guile -*-
(use-modules (ice-9 format))
(use-modules (srfi srfi-41))

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

(define (square x) (* x x))
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

(define (fix/sqrt-iter guess last-guess x)
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

