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

