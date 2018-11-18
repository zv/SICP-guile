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

