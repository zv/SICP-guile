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


