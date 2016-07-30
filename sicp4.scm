;;; -*- mode: scheme; coding: utf-8; -*-
#| Structure and Interpretation of Computer Programs - Chapter 4 |#
(use-modules (ice-9 format))
(use-modules (ice-9 match))
(use-modules (ice-9 pretty-print))
(use-modules (srfi srfi-1))
(use-modules (oop goops))


(define (inc a) (+ a 1))
(define (curry fn . c-args)
  (λ args
    (apply fn (append c-args args))))

(define inside-repl?
  ;; current-source-location is formatted in a line, column, filename alist
  ;; e.g ((line . INTEGER) (column . INTEGER) (filename . SYMBOL|FALSE))
  (eq? #f (assq-ref (current-source-location) 'filename)))



;; Custom Macros & Utils
(define-syntax generate-accessors
  (syntax-rules (generate-accessors define exp)
    ((generate-accessors ()) #t)

    ((generate-accessors ((fn def) . remaining))
     (begin
       (define (fn exp) (def exp))
       (generate-accessors remaining)))

    ((generate-accessors non-list)
     (syntax-error "not a list"))))

(define-syntax assert
	(syntax-rules ()
    ((assert x y0 ...)
     (if (not x) (error "Assertion failed" 'x y0 ...))) ))

(define (test-equal x y)
  (assert (equal? x y)))

(define (test-eq x y)
  (assert (eq? x y)))

;; Construct a piece of syntax (essentially just a quasiquote wrapper)
(define-syntax %as-syntax
  (syntax-rules ()
    ((%as-syntax exp)
     `exp)))


;; Section 4.1
(include "/home/zv/z/practice/sicp/4/base-evaluator.scm")
;; Add arithmetic
(append! primitive-procedures
         `((+ ,+) (- ,-) (* ,*) (/ ,/) (abs ,abs)
           (= ,=) (< ,<) (<= ,<=) (> ,>) (> ,>=)
           (not ,not)
           (list ,list)
           (member ,member)
           (display ,display)))

#| Exercise 4.1
Notice that we cannot tell whether the metacircular evaluator evaluates operands
from left to right or from right to left. Its evaluation order is inherited from
the underlying Lisp: If the arguments to cons in list-of-values are evaluated
from left to right, then list-of-values will evaluate operands from left to
right; and if the arguments to cons are evaluated from right to left, then
list-of-values will evaluate operands from right to left.

Write a version of list-of-values that evaluates operands from left to right
regardless of the order of evaluation in the underlying Lisp. Also write a
version of list-of-values that evaluates operands from right to left. |#

;; There are multiple ways to approach this, Erlang generally recommends
;; "prereversing", but this has always struck me as very dirty, so I iterate
;; backwards. |#
(define (rtl-list-of-values exps env)
  (if (no-operands? exps) '()
      (let* ((left (zeval (first-operand exps) env) )
             (right (rtl-list-of-values (rest-operands exps) env) ))
        (cons left right))))


#| Exercise 4.2
Louis Reasoner plans to reorder the cond clauses in eval so that the clause for
procedure applications appears before the clause for assignments. He argues that
this will make the interpreter more efficient: Since programs usually contain
more applications than assignments, definitions, and so on, his modified eval
will usually check fewer clauses than the original eval before identifying the
type of an expression.

1. What is wrong with Louis’s plan? (Hint: What will Louis’s evaluator do with the
expression (define x 3)?)

2. Louis is upset that his plan didn’t work. He is willing to go to any lengths to
make his evaluator recognize procedure applications before it checks for most
other kinds of expressions. Help him by changing the syntax of the evaluated
language so that procedure applications start with call. For example, instead of
(factorial 3) we will now have to write (call factorial 3) and instead of (+ 1 2)
we will have to write (call + 1 2). |#

#| Answer:
1: The order of operations will cause some variables to be undefined. As the
example suggests, define will be called with 'x' and '3' as arguments. `define'
cannot be made into a procedure because the arguments will be evaluated.

2. Only `application' need be changed:

(define application? (exp)
  (tagged-list? exp 'call))
(define operator (exp) (cadr exp))
(define operands (exp) (cddr exp)) |#


#| Exercise 4.3
Rewrite eval so that the dispatch is done in data-directed style. Compare this
with the data-directed differentiation procedure of Exercise 2.73.
(You may use the car of a compound expression as the type of the expression, as
     is appropriate for the syntax implemented in this section.) |#
(define-class <dispatch-table> ()
  (method-table #:init-value (make-hash-table)
                #:getter method-table))

(define (table-ordinal op type)
  (let ([opstr   (symbol->string op)]
        [typestr (symbol->string type)])
    (string-append opstr "/" typestr)))

(define-method (get (dt <dispatch-table>) op type)
  (if (and (symbol? op) (symbol? type))
      (hash-ref (method-table dt) (table-ordinal op type))
      #f))

(define-method (put (dt <dispatch-table>) op type item)
  (hash-set! (method-table dt) (table-ordinal op type) item))

(define dispatch-tt (make <dispatch-table>))

(define (list-tag expr)
  "Extract the type of expression"
  (if (pair? expr) (car expr) #f))

(define (install-procedure p)
  (put dispatch-tt 'eval (car p) (cadr p)))

;; Install our procedures
(map
 install-procedure
 `([quote  ,(λ (expr env) (text-of-quotation expr))]
   [set!    ,eval-assignment]
   [define ,eval-definition]
   [if     ,eval-if]
   [lambda ,(λ (expr env) (make-procedure (lambda-parameters expr) (lambda-body expr) env))]
   [begin  ,(λ (expr env) (eval-sequence (begin-actions expr) env))]
   [cond   ,(λ (expr env) (zeval (cond->if expr) env))]))

(define (zeval expr env)
  (let ([dispatch-fn (get dispatch-tt 'eval (list-tag expr))])
    (cond
     [(self-evaluating? expr)
      expr]
     [(variable? expr)
      (lookup-variable-value expr env)]
     [(procedure? dispatch-fn)
      (dispatch-fn expr env)]
     [(application? expr)
      (zapply (zeval (operator expr) env)
              (list-of-values (operands expr) env))]
     [else (error "Bad Expression" expr)])))

(define (install-driver-loop evaluator fn)
  (put dispatch-tt 'driver-loop evaluator fn))

(install-driver-loop 'zeval base-driver-loop)

#| Exercise 4.4
Recall the definitions of the special forms and and or from Chapter 1:

`and': The expressions are evaluated from left to right. If any expression
evaluates to false, false is returned; any remaining expressions are not
evaluated. If all the expressions evaluate to true values, the value of the last
expression is returned. If there are no expressions then true is returned.
`or': The expressions are evaluated from left to right. If any expression
evaluates to a true value, that value is returned; any remaining expressions are
not evaluated. If all expressions evaluate to false, or if there are no
expressions, then false is returned.

Install `and' and `or' as new special forms for the evaluator by defining
appropriate syntax procedures and evaluation procedures eval-and and eval-or.
Alternatively, show how to implement and and or as derived expressions. |#
(define (disjunct exp)
  (if (null? (cdr exp)) 'false
      (cadr exp)))

(define (rest-disjunctions exp)
  (if (null? (cdr exp)) '()
      (cddr exp)))

;; or
(define (or? exp) (tagged-list? exp 'or))
(define (eval-or exp env) (eval-connective exp env true?))
(install-procedure `(or ,eval-or))

;; and
(define (and? exp) (tagged-list? exp 'and))
(define (eval-and exp env) (eval-connective exp env false?))
(install-procedure `(and ,eval-and))

(define (eval-connective exp env oper)
  "eval-connective evaluates the first part of an expression in the given
environment. If the result applied to `oper' is false, it continues to evaluate
until `(oper exp)' argument returns true or no arguments remain."
  (let ([disjunction (zeval (disjunct exp) env)]
        [rest-disjunctions (rest-disjunctions exp)])
    (if (or (oper disjunction) (null? rest-disjunctions)) disjunction
        (eval-connective (cons (operator exp) rest-disjunctions)
                         env
                         oper))))


#| Exercise 4.5
Scheme allows an additional syntax for cond clauses, (⟨test⟩ => ⟨recipient⟩). If
⟨test⟩ evaluates to a true value, then ⟨recipient⟩ is evaluated. Its value must
be a procedure of one argument; this procedure is then invoked on the value of
the ⟨test⟩, and the result is returned as the value of the cond expression. For
example

     (cond ((assoc 'b '((a 1) (b 2))) => cadr)
          (else false))

returns 2.
Modify the handling of cond so that it supports this extended syntax. |#

(define (cond-is-pipe? exp)
  (if (pair? exp) (eq? (cadr exp) '=>) #f))

(define (cond-recipient exp) (caddr exp))

(define (expand-clauses clauses)
  (if (null? clauses) 'false
      (let ([first (car clauses)]
            [rest  (cdr clauses)])

        ;; check for =>
        (if (cond-is-pipe? first)
            (let ([test (cond-predicate first)])
              (make-if test
                       (list (cond-recipient first) test)
                       (expand-clauses rest)))

            ;; otherwise a normal cond applies
            (if (cond-else-clause? first)
                (if (null? rest) (sequence->exp (cond-actions first))
                    (error "ELSE clause isn't last: COND->IF" clauses))
                (make-if (cond-predicate first)
                         (sequence->exp (cond-actions first))
                         (expand-clauses rest)))))))

#| Exercise 4.6
Let expressions are derived expressions, because

    (let ((⟨var₁⟩ ⟨exp₁⟩) … (⟨varₙ⟩ ⟨expₙ⟩))
      ⟨body⟩)

is equivalent to

    ((lambda (⟨var₁⟩ … ⟨varₙ⟩)
       ⟨body⟩)
     ⟨exp₁⟩
     …
     ⟨expₙ⟩)

Implement a syntactic transformation let->combination that reduces evaluating
let expressions to evaluating combinations of the type shown above, and add the
appropriate clause to eval to handle let expressions. |#

(generate-accessors
 ([let-bindings       cadr]
  [let-body           cddr]
  [let-binding-vars   (curry map car)]
  [let-binding-exprs  (curry map cadr)]
  [let-vars           (compose let-binding-vars let-bindings)]
  [let-exprs          (compose let-binding-exprs let-bindings)]))


(define (make-let->lambda vars exprs body)
  "Makes a let expression as ((lambda (vars) body) exprs)"
  (cons (make-lambda vars body) exprs))

(define (let->combination exp)
  (if (null? exp) 'false
      (let ([bindings (let-bindings exp)]
            [body     (let-body exp)])
        (make-let->lambda (let-binding-vars bindings)
                          (let-binding-exprs bindings)
                          body))))

(install-procedure `(let ,(λ (exp env) (zeval (let->combination exp) env))))

#| Exercise 4.7
`let*' is similar to `let', except that the bindings of the `let*' variables are
performed sequentially from left to right, and each binding is made in an
environment in which all of the preceding bindings are visible. For example

    (let* ((x 3)
           (y (+ x 2))
           (z (+ x y 5)))
      (* x z))

returns 39. Explain how a `let*' expression can be rewritten as a set of nested
let expressions, and write a procedure `let*->nested-lets' that performs this
transformation. If we have already implemented let (Exercise 4.6) and we want to
extend the evaluator to handle `let*', is it sufficient to add a clause to eval
whose action is

    (eval (let*->nested-lets exp) env)

(let (x 3)
  (let (y 2)
    1))

((lambda (x) (lambda (y) 1) 2) 3)

or must we explicitly expand `let*' in terms of non-derived expressions? |#

;;; There is nothing preventing `let*' from being defined in terms of existing
;;; `let' expressions
(generate-accessors
 ([let*-body  caddr]
  [let*-inits cadr]))

;;;; This is a little funky here, I've replaced this with another version copied
;;;; online -- the only thing wrong with this is some monkeying around with the let
;;;; order
;; (define (let*->nested-let exp)
;;   (define (next exp)
;;     (list (operator exp) (cdadr exp) (caddr exp)))
;;   (if (null? exp) 'false
;;       (let ([bindings (let-bindings exp)]
;;             [body     (let-body exp)])
;;         (if (null? bindings) body
;;             (make-let->lambda
;;              (list (car (let-binding-vars bindings)))
;;              (list (car (let-binding-exprs bindings)))
;;              (let*->nested-let (next exp)))))))
(define (let*->nested-lets expr)
  (let ([inits (let*-inits expr)]
        [body (let*-body expr)])
    (define (next expr)
      (if (null? expr) body
          (list 'let (list (car expr)) (next (cdr expr)))))
    (next inits)))


(install-procedure `(let* ,(λ (exp env) (zeval (let*->nested-lets exp) env))))

#| Exercise 4.8
“Named let” is a variant of let that has the form

    (let ⟨var⟩ ⟨bindings⟩ ⟨body⟩)

The ⟨bindings⟩ and ⟨body⟩ are just as in ordinary let, except that ⟨var⟩ is
bound within ⟨body⟩ to a procedure whose body is ⟨body⟩ and whose parameters are
the variables in the ⟨bindings⟩. Thus, one can repeatedly execute the ⟨body⟩ by
invoking the procedure named ⟨var⟩. For example, the iterative Fibonacci
procedure (1.2.2) can be rewritten using named let as follows:

    (define (fib n)
      (let fib-iter ((a 1) (b 0) (count n))
        (if (= count 0)
            b
            (fib-iter (+ a b)
                      a
                      (- count 1)))))

Modify let->combination of Exercise 4.6 to also support named let. |#
(define (named-let? exp) (symbol? (cadr exp)))
(generate-accessors
 ([nlet-var cadr]
  [nlet-bindings caddr]
  [nlet-body cdddr]))

(define (make-named-let exp)
  ;; get prepped for that long let
  (let* ([body       (nlet-body exp)]
         [bindings   (nlet-bindings exp)]
         [vars       (let-binding-vars bindings)]
         [exprs      (let-binding-exprs bindings)]
         [fnname     (nlet-var exp)]
         [fn         (make-lambda vars body)])
    (%as-syntax
     (let ,bindings
       (begin
         (define ,fnname ,fn)
         ,@body)))))

(define (let->combination exp)
  (if (null? exp) 'false
      (if (named-let? exp) (make-named-let exp)
          ;; otherwise we're processing a normal let
          (make-let->lambda (let-vars exp)
                            (let-exprs exp)
                            (let-body exp)))))

#| Exercise 4.9
Many languages support a variety of iteration constructs, such as `do', `for',
`while', and `until'. In Scheme, iterative processes can be expressed in terms of
ordinary procedure calls, so special iteration constructs provide no essential
gain in computational power. On the other hand, such constructs are often
convenient. Design some iteration constructs, give examples of their use, and
show how to implement them as derived expressions. |#
(generate-accessors
 ([while-cond cadr]
  [while-body caddr]))

(define (make-while exp)
  (let ([body (while-body exp)]
        [cond (while-cond exp)])
    (if (null? cond) 'false
        (%as-syntax
         (let while-loop ()
           (if ,cond
               (begin ,body
                      (while-loop))
               false))))))

(install-procedure `(while ,(λ (exp env) (zeval (make-while exp) env))))

#| Exercise 4.11 & Exercise 4.12
  4.11: Instead of representing a frame as a pair of lists, we can represent a
  frame as a list of bindings, where each binding is a name-value pair. Rewrite
  the environment operations to use this alternative representation.

  4.12: The procedures define-variable!, set-variable-value! and
  lookup-variable-value can be expressed in terms of more abstract procedures for
  traversing the environment structure. Define abstractions that capture the
  common patterns and redefine the three procedures in terms of these
  abstractions. |#
(define (make-frame variables values)
  (map cons variables values))

(define (var-process var environment fn)
  (define (var-search env)
    (if (eq? env the-empty-environment) (begin
                                          ;;(pretty-print environment)
                                          (error "Unbound variable" var))
        (let* ([frame (first-frame env)]
               [entry (assoc var frame)])
          (if entry (fn frame entry)
              (var-search (enclosing-environment env))))))
  (var-search environment))

(define (lookup-variable-value var env)
  (var-process var env (λ (_frame entry) (cdr entry))))

(define (set-variable-value! var val env)
  (var-process var env (λ (frame entry) (set-cdr! entry val))))

(define (define-variable! var val env)
  (set-car! env (assoc-set! (first-frame env) var val)))


#| Exercise 4.13
Scheme allows us to create new bindings for variables by means of define, but
provides no way to get rid of bindings. Implement for the evaluator a special
form make-unbound! that removes the binding of a given symbol from the
environment in which the make-unbound! expression is evaluated. This problem is
not completely specified. For example, should we remove only the binding in the
first frame of the environment? Complete the specification and justify any
choices you make. |#

#| - - - - - Spec:
`undefine' and `unset' are functions that set the name of the binding inside the
closest stack-frame to null. |#
(define (undefine-variable! var env)
  (var-process var env (λ (frame entry) (set-car! entry '()))))

(define (eval-undefinition exp env)
  (undefine-variable!
   (definition-variable exp) env)
  'ok)

(install-procedure `(undefine ,eval-undefinition))

#| Exercise 4.14
Eva Lu Ator and Louis Reasoner are each experimenting with the metacircular
evaluator. Eva types in the definition of map, and runs some test programs that
use it. They work fine. Louis, in contrast, has installed the system version of
map as a primitive for the metacircular evaluator. When he tries it, things go
terribly wrong. Explain why Louis’s map fails even though Eva’s works. |#

#| - - - - - Solution:
Louis is trying to use a variable defined inside the *interpreters* stack frame,
not the *interpreTED* stack frame |#


#| Exercise 4.15
Given a one-argument procedure p and an object a, p is said to “halt” on a if
evaluating the expression (p a) returns a value (as opposed to terminating with
an error message or running forever). Show that it is impossible to write a
procedure halts? that correctly determines whether p halts on a for any
procedure p and object a. Use the following reasoning: If you had such a
procedure halts?, you could implement the following program:

  (define (run-forever)
    (run-forever))

  (define (try p)
    (if (halts? p p)
        (run-forever)
        'halted))

Now consider evaluating the expression (try try) and show that any possible
outcome (either halting or running forever) violates the intended behavior of
halts?. |#

#| - - - - - Solution:
This problem is an abstract description of a thought experiment Turing conducted in the 1930s which would later be known as the 'halting problem'.

The problem has no solution for a similar reason to the 'liar' paradox:

Suppose it returns true -- `try' enters an endless loop, so it obviously doesn’t halt, while halts? returned true. The contrawise position is identical

Therefore there can be no solution to the problem |#


#| Exercise 4.16
In this exercise we implement the method just described for interpreting
internal definitions. We assume that the evaluator supports let (see Exercise
                                                                     4.6).

1. Change `lookup-variable-value' (4.1.3) to signal an error if the value it finds
is the symbol *unassigned*.
2. Write a procedure `scan-out-defines' that takes a procedure body and returns an
equivalent one that has no internal definitions, by making the transformation
described above.
3. Install `scan-out-defines' in the interpreter, either in make-procedure or in
procedure-body (see 4.1.3). Which place is better? Why? |#
;; 1. Solution
(define (simultaneous/lookup-variable-value var env)
  (var-process var env (λ (_f entry)
                         (if (eq? (cdr entry) '*unassigned*)
                             (error "Unassigned var: " var)
                             (cdr entry)))))

;; 2
(define (scan-out-defines expr)
  "Transform a procedure, returning an equivalent one with no internal
definitions"
  (define has-define (find (λ (e) (and (pair? e) (eq? (car e) 'define)))
                           expr))
  (if has-define
      (fold
       (λ (elt prev)
         (let ([bindings (let-bindings prev)]
               [body     (let-body prev)])
           ;; merge our (new) bindings & body
           (match elt
             [('define var val)
              `(let ((,var '*unassigned*)
                     ,@bindings)
                 (set! ,var ,val)
                 ;; we use ,@ to prevent recursive lists
                 ,@body)]
             [_ `(let ,bindings ,@body ,elt)])))
       '(let ()) ;; we start with a basic let expression
       expr)
      expr))

;; simulatanous test
(test-equal
    (scan-out-defines '((define a 1)
                        (make-thing 1)
                        (define b 2)
                        (define c 3)
                        (make-thing a 1)))
  '(let ((c '*unassigned*)
         (b '*unassigned*)
         (a '*unassigned*))
     (set! c 3)
     (set! b 2)
     (set! a 1)
     (make-thing 1)
     (make-thing a 1)))

;; 3 -- I've selected make-procedure so that the conversion is done at
;; interpretation, rather than runtime.
(define (simultaneous/make-procedure parameters body env)
  (list 'procedure
        parameters
        (scan-out-defines body)
        env))

#| Exercise 4.18
Consider an alternative strategy for scanning out definitions that translates
the example in the text to

(lambda ⟨vars⟩
  (let ((u '*unassigned*)
        (v '*unassigned*))
    (let ((a ⟨e1⟩)
          (b ⟨e2⟩))
      (set! u a)
      (set! v b))
    ⟨e3⟩))

Here a and b are meant to represent new variable names, created by the
interpreter, that do not appear in the user’s program. Consider the solve
procedure from 3.5.4:

(define (solve f y0 dt)
  (define y (integral (delay dy) y0 dt))
  (define dy (stream-map f y))
  y)

Will this procedure work if internal definitions are scanned out as shown in
this exercise? What if they are scanned out as shown in the text? Explain. |#

; - - - - - - Solution:
;; This wont work because the proxy-value of `y' (a) cannot be directly
;; referenced upon the definition of `dy'


#| Exercise 4.19
Ben Bitdiddle, Alyssa P. Hacker, and Eva Lu Ator are arguing about the desired
result of evaluating the expression

  (let ((a 1))
    (define (f x)
      (define b (+ a x))
      (define a 5)
      (+ a b))
    (f 10))

Ben asserts that the result should be obtained using the sequential rule for
define: `b' is defined to be 11, then `a' is defined to be 5, so the result is
16. Alyssa objects that mutual recursion requires the simultaneous scope rule
for internal procedure definitions, and that it is unreasonable to treat
procedure names differently from other names. Thus, she argues for the mechanism
implemented in Exercise 4.16. This would lead to a being unassigned at the time
that the value for `b' is to be computed. Hence, in Alyssa’s view the procedure
should produce an error. Eva has a third opinion. She says that if the
definitions of `a' and `b' are truly meant to be simultaneous, then the value 5
for `a' should be used in evaluating b. Hence, in Eva’s view `a' should be 5, `b'
should be 15, and the result should be 20. Which (if any) of these viewpoints do
you support? Can you devise a way to implement internal definitions so that they
behave as Eva prefers? |#

#| Solution
I like Alyssas view, although Ben's dominates most thinking.
|#

;; Eva's view can be easily supported by swapping the order within the `let'
;; quasiquote of `set!' and `@,body'


#| Exercise 4.20 (lol)
Because internal definitions look sequential but are actually simultaneous, some
people prefer to avoid them entirely, and use the special form letrec instead.
Letrec looks like let, so it is not surprising that the variables it binds are
bound simultaneously and have the same scope as each other. The sample procedure
f above can be written without internal definitions, but with exactly the same
meaning, as

  (define (f x)
    (letrec
        ((even?
          (lambda (n)
            (if (= n 0)
                true
                (odd? (- n 1)))))
        (odd?
          (lambda (n)
            (if (= n 0)
                false
                (even? (- n 1))))))
      ⟨rest of body of f⟩))

`letrec' expressions, which have the form

  (letrec ((⟨var₁⟩ ⟨exp₁⟩) … (⟨varₙ⟩ ⟨expₙ⟩))
    ⟨body⟩)

are a variation on let in which the expressions ⟨expₖ⟩ that provide the initial
values for the variables ⟨varₖ⟩ are evaluated in an environment that includes
all the letrec bindings. This permits recursion in the bindings, such as the
mutual recursion of even? and odd? in the example above, or the evaluation of 10
factorial with

  (letrec
      ((fact
        (lambda (n)
          (if (= n 1)
              1
              (* n (fact (- n 1)))))))
    (fact 10))

1. Implement letrec as a derived expression, by transforming a letrec expression
into a let expression as shown in the text above or in Exercise 4.18. That is,
the letrec variables should be created with a let and then be assigned their
values with set!.

2. Louis Reasoner is confused by all this fuss about internal definitions. The
way he sees it, if you don’t like to use define inside a procedure, you can just
use let. Illustrate what is loose about his reasoning by drawing an environment
diagram that shows the environment in which the ⟨rest of body of f⟩ is evaluated
during evaluation of the expression (f 5), with f defined as in this exercise.
Draw an environment diagram for the same evaluation, but with let in place of
letrec in the definition of f. |#

;; 1.
(define (letrec->let expr)
  (%as-syntax
   (let
       ,(map ; generate the (binding . '*unassigned) let binds
         (λ (v) (list v ''*unassigned))
         (map car (cadr expr)))

     ,@(map ; generate the `set!' expressions
        (λ (bind) `(set! ,(car bind) ,(cadr bind)))
        (let-bindings expr))

     ;; and merge our existing body
     ,@(let-body expr))))

(test-equal
    (letrec->let
     `(letrec ((a (lambda () (b)))
               (b (lambda () (a))))
        (x a)
        (x b)
        (x c)))

  '(let ((a '*unassigned)
         (b '*unassigned))
     (set! a (lambda () (b)))
     (set! b (lambda () (a)))
     (x a)
     (x b)
     (x c)))

(install-procedure `(letrec ,(λ (exp env) (zeval (letrec->let exp) env))))
;; 2.
;; The main problem with Louis's reasoning is that the environment that `let' is
;; being evaluating against is actually expressed in the form of a `lambda' whoses
;; actual function bodies are being passed in as arguments (in the case of (f x)),
;; this means that the lexical scope of `even?' cannot see that of `odd?' and
;; versa.


#| Exercise 4.21
Amazingly, Louis’s intuition in Exercise 4.20 is correct. It is indeed possible
to specify recursive procedures without using letrec (or even define), although
the method for accomplishing this is much more subtle than Louis imagined. The
following expression computes 10 factorial by applying a recursive factorial
procedure:231

  ((lambda (n)
    ((lambda (fact) (fact fact n))
      (lambda (ft k)
        (if (= k 1)
            1
            (* k (ft ft (- k 1)))))))
  10)

1. Check (by evaluating the expression) that this really does compute
factorials. Devise an analogous expression for computing Fibonacci numbers.

Consider the following procedure, which includes mutually recursive internal
definitions:

    (define (f x)
      (define (even? n)
        (if (= n 0)
            true
            (odd? (- n 1))))
      (define (odd? n)
        (if (= n 0)
            false
            (even? (- n 1))))
      (even? x))

2. Fill in the missing expressions to complete an alternative definition of f,
which uses neither internal definitions nor letrec:

    (define (f x)
      ((lambda (even? odd?)
         (even? even? odd? x))
       (lambda (ev? od? n)
         (if (= n 0)
             true
             (od? ⟨??⟩ ⟨??⟩ ⟨??⟩)))
       (lambda (ev? od? n)
         (if (= n 0)
             false
             (ev? ⟨??⟩ ⟨??⟩ ⟨??⟩))))) |#

;; 1.
;; It does indeed produce Factorials
(define funk-fibonacci
  (λ (n) ;; (it's a fibonacci number)
    ((λ (fib) (fib fib n))
     (λ (fb k)
       (match k
         [0 1]
         [1 1]
         [_ (+ (fb fb (- k 1))
               (fb fb (- k 2)))])))))

;; 2.
(define (feven-4.21 x)
  ((λ (even? odd?)
     (even? even? odd? x))
   (λ (ev? od? n)
     (if (= n 0)
         #t
         (od? ev? od? (- n 1))))
   (λ (ev? od? n)
     (if (= n 0)
         #f
         (ev? ev? od? (- n 1))))))

(assert (= (funk-fibonacci 4) 5))
(assert (feven-4.21 4))


;; 4.1.3 - Separating Syntactic Analysis from Execution
(include "/home/zv/z/practice/sicp/4/evaluator-analyzer.scm")

(define (install-analyze-procedure p)
  (put dispatch-tt 'analyze (car p) (cadr p)))

(map install-analyze-procedure
     `([set!   ,analyze-assignment]
       [define ,analyze-definition]
       [if     ,analyze-if]
       [lambda ,analyze-lambda]
       [begin  ,(λ (exp) (analyze-sequence (begin-actions exp)))]
       [cond   ,(λ (exp) (analyze (cond->if exp)))]))

;; redefine analyze with data-driven variable exps
(define (analyze exp)
  (let ([dispatch-fn (get dispatch-tt 'analyze (list-tag exp))])
    (cond
     [(self-evaluating? exp)
      (analyze-self-evaluating exp)]
     [(quoted? exp)
      (analyze-quoted exp)]
     [(variable? exp)
      (analyze-variable exp)]
     [(procedure? dispatch-fn)
      (dispatch-fn exp)]
     [(application? exp)
      (analyze-application exp)]
     [else
      (error "Unknown expression type: ANALYZE" exp)])))

(define (aeval exp env) ((analyze exp) env))

(define (aeval-driver-loop)
  (prompt-for-input ";;; Analyzing(aeval) input:")
  (let ((input (read)))
    (let ((output
           (aeval input
                  the-global-environment)))
      (announce-output output-prompt)
      (user-print output)))
  (aeval-driver-loop))

(install-driver-loop 'aeval aeval-driver-loop)

#| Exercise 4.22
Extend the evaluator in this section to support the special form let. (See Exercise 4.6.) |#
(install-analyze-procedure `(let ,(λ (exp) (analyze (let->combination exp)))))


;; ------------------------------------------------------------|
;; Section 4.2 - Variations on a Scheme                        |
;; ------------------------------------------------------------|

;; 4.2.1 -- Normal Order and Applicative Order

#| Exercise 4.25
Suppose that (in ordinary applicative-order Scheme) we define unless as shown
above and then define factorial in terms of unless as

  (define (factorial n)
    (unless (= n 1)
      (* n (factorial (- n 1)))
      1))
What happens if we attempt to evaluate (factorial 5)? Will our definitions work
in a normal-order language? |#

;; Solution:

;; Applicative order languages will cause an infinite loop with the definition
;; of `unless' provided by SICP -- on the other hand a normal-order language will
;; do just fine


#| Exercise 4.26
Ben Bitdiddle and Alyssa P. Hacker disagree over the importance of lazy
evaluation for implementing things such as unless. Ben points out that it’s
possible to implement unless in applicative order as a special form. Alyssa
counters that, if one did that, unless would be merely syntax, not a procedure
that could be used in conjunction with higher-order procedures. Fill in the
details on both sides of the argument. Show how to implement unless as a derived
expression (like cond or let), and give an example of a situation where it might
be useful to have unless available as a procedure, rather than as a special
form. |#
(define (zv-unless condition consequent alternative)
  (if condition alternative
      consequent))

(generate-accessors
 ([unless-predicate cadr]
  [unless-alternative caddr]))

(define (unless-consequent exp)
  (if (not (null? (cdddr exp)))
      (cadddr exp)
      'false))

(define (unless->if exp)
  (make-if
   (unless-predicate exp)
   (unless-consequent exp)
   (unless-alternative exp)))

(define (analyze-unless exp)
  (let ([pproc (analyze (unless-predicate exp))]
        [cproc (analyze (unless-consequent exp))]
        [aproc (analyze (unless-alternative exp))])
    (lambda (env)
      (if (true? (pproc env))
          (cproc env)
          (aproc env)))))

(install-procedure `(unless ,(λ (exp env) (zeval (unless->if exp) env))))
(install-analyze-procedure `(unless ,analyze-unless))

;; this functions utility is for lazy bums who cant type `not'
;; Various evaluator utils

;; Lazy Evaluator
(include "/home/zv/z/practice/sicp/4/lazy-evaluator.scm")

;; Install our new driver-loop
(define (lazy-driver-loop)
  (prompt-for-input ";; Lazy (leval) input: ")
  (let* ((input (read))
         (output (actual-value input the-global-environment)))
      (announce-output output-prompt)
      (user-print output))
  (lazy-driver-loop))

(install-driver-loop 'leval lazy-driver-loop)

#| Exercise 4.27
Suppose we type in the following definitions to the lazy evaluator:

  (define count 0)
  (define (id x) (set! count (+ count 1)) x)
  (define w (id (id 10)))

Give the missing values in the following sequence of interactions, and explain
your answers.


  ;;; L-Eval input:
  count

  ;;; L-Eval value:
  1

  ;;; L-Eval input:
  w

  ;;; L-Eval value:
  10

  ;;; L-Eval input:
  count

  ;;; L-Eval value:
  2
|#

#| Exercise 4.28
lazy-eval uses actual-value rather than leval to evaluate the operator before passing
it to apply, in order to force the value of the operator. Give an example that
demonstrates the need for this forcing.
|#

;; Solution
;; Any function using a lambda as an argument will fail -- the operands are not forced and when trying to apply them you will attempt to apply a thunk instead of a "real" value.

#| Exercise 4.29
Exhibit a program that you would expect to run much more slowly without
memoization than with memoization. Also, consider the following interaction,
where the id procedure is defined as in Exercise 4.27 and count starts at 0:

  (define (square x) (* x x))

;;; L-Eval input:
  (square (id 10))

;;; L-Eval value:
  ⟨response⟩

;;; L-Eval input:
  count

;;; L-Eval value:
  ⟨response⟩

Give the responses both when the evaluator memoizes and when it does not.
|#

;; Solutions

;; The canonical example of a function sped up by memoization is factorial --
;; each of the components can be reused n^2 times


#| Memoized:
;;; L-Eval input:
(square (id 10))

;;; L-Eval value:
100

;;; L-Eval input:
count

;;; L-Eval value:
1
|#

#| Raw:

;;; L-Eval input:
  (square (id 10))

;;; L-Eval value:
  100

;;; L-Eval input:
  count

;;; L-Eval value:
  2

|#

#| Exercise 4.30
Cy D. Fect, a reformed C programmer, is worried that some side effects may never
take place, because the lazy evaluator doesn’t force the expressions in a
sequence. Since the value of an expression in a sequence other than the last one
is not used (the expression is there only for its effect, such as assigning to a
variable or printing), there can be no subsequent use of this value (e.g., as an
argument to a primitive procedure) that will cause it to be forced. Cy thus
thinks that when evaluating sequences, we must force all expressions in the
sequence except the final one. He proposes to modify eval-sequence from 4.1.1 to
use actual-value rather than eval:

  (define (eval-sequence exps env)
    (cond ((last-exp? exps)
          (eval (first-exp exps) env))
          (else
          (actual-value (first-exp exps)
                        env)
          (eval-sequence (rest-exps exps)
                          env))))

1. Ben Bitdiddle thinks Cy is wrong. He shows Cy the for-each procedure
described in Exercise 2.23, which gives an important example of a sequence with
side effects:

    (define (for-each proc items)
      (if (null? items)
          'done
          (begin (proc (car items))
                 (for-each proc
                           (cdr items)))))

He claims that the evaluator in the text (with the original eval-sequence)
handles this correctly:

    ;;; L-Eval input:
    (for-each
     (lambda (x) (newline) (display x))
     '(57 321 88))
    57
    321
    88

    ;;; L-Eval value:
    done

Explain why Ben is right about the behavior of for-each.

2. Cy agrees that Ben is right about the for-each example, but says that that’s
not the kind of program he was thinking about when he proposed his change to
eval-sequence. He defines the following two procedures in the lazy evaluator:

    (define (p1 x)
      (set! x (cons x '(2)))
      x)

    (define (p2 x)
      (define (p e) e x)
      (p (set! x (cons x '(2)))))

What are the values of (p1 1) and (p2 1) with the original eval-sequence?
What would the values be with Cy’s proposed change to eval-sequence?

3. Cy also points out that changing eval-sequence as he proposes does not affect
the behavior of the example in part a. Explain why this is true.

4. How do you think sequences ought to be treated in the lazy evaluator? Do you
like Cy’s approach, the approach in the text, or some other approach?
|#

#| Solutions
1. In `for-each's case, the procedure is called every time, all primitive
procedures are called -- even if they are the last.

2.
leval: (p1 1) => (1 2); (p2 1) => 1
(`e' is never evaluated -- it's a compound procedure)
actual-value: (p1 1) => (1 2); (p2 1) => (1 2)

3. There is no difference -- primitive procedures are called either way

4. Side effects are a critical aspect of computer programming -- a lazy computer
system needs to execute them in a manner consistent with our expectations of a
basic interpreter -- Cy's approach is the winner. |#

#| Exercise 4.31
The approach taken in this section is somewhat unpleasant, because it makes an
incompatible change to Scheme. It might be nicer to implement lazy evaluation as
an upward-compatible extension, that is, so that ordinary Scheme programs will
work as before. We can do this by extending the syntax of procedure declarations
to let the user control whether or not arguments are to be delayed. While we’re
at it, we may as well also give the user the choice between delaying with and
without memoization. For example, the definition

  (define (f a (b lazy) c (d lazy-memo))
    …)

would define f to be a procedure of four arguments, where the first and third
arguments are evaluated when the procedure is called, the second argument is
delayed, and the fourth argument is both delayed and memoized. Thus, ordinary
procedure definitions will produce the same behavior as ordinary Scheme, while
adding the lazy-memo declaration to each parameter of every compound procedure
will produce the behavior of the lazy evaluator defined in this section. Design
and implement the changes required to produce such an extension to Scheme. You
will have to implement new syntax procedures to handle the new syntax for
define. You must also arrange for eval or apply to determine when arguments are
to be delayed, and to force or delay arguments accordingly, and you must arrange
for forcing to memoize or not, as appropriate.
|#
(define (perpetual-thunk? obj) (tagged-list? obj 'always-thunk))
(define (delay-it-perpetually exp env)
  (list 'always-thunk exp env))

(define (list-of-resolved-args parameters arguments env)
  (map
   (λ (p a)
     (match p
       [(_ 'lazy)       (delay-it-perpetually a env)]
       [(_ 'lazy-memo)  (delay-it a env)]
       [_               a]))
   parameters
   arguments))

(define (force-it obj)
  "This is just a memoizing version of `force-it'"
  (define (fetch-result e)
    (actual-value (thunk-exp e) (thunk-env e)))
  (match obj
    [thunk?
     (let ([result (fetch-result obj)])
       (set! obj `(evaluated-thunk ,result))
       result)]
    [evaluated-thunk? (thunk-value obj)]
    [perpetual-thunk? (fetch-result obj)]
    [_ obj]))

(define (fetch-parameter p) (if (pair? p) (car p) p))
(define (extract-parameters fn)
  (map fetch-parameter (procedure-parameters fn)))

(define (capply procedure arguments env)
  "capply is a combined `apply' function -- determining which parameters are
lazy, memoized or raw and supplying them to the function at hand"
  ;;(format #t "procedure: ~a\narguments: ~a\nenv: ~a" procedure arguments env)
  (cond ((primitive-procedure? procedure)
         (apply-primitive-procedure
          procedure
          (list-of-arg-values arguments env)))  ; changed
        ((compound-procedure? procedure)
         (leval-sequence
          (procedure-body procedure)
          (extend-environment
           (extract-parameters procedure)
           (list-of-resolved-args (procedure-parameters procedure)
                                  arguments
                                  env) ; changed
           (procedure-environment procedure))))
        (else (error "Unknown procedure type: APPLY" procedure))))

;; Install our new driver-loop
(define (combined-driver-loop)
  (prompt-for-input ";; Strict/Lazy (ceval) input: ")
  (let* ((input (read))
         (output (actual-value input the-global-environment)))
    (announce-output output-prompt)
    (user-print output))
  (combined-driver-loop))

(install-driver-loop 'ceval combined-driver-loop)

                                        ; Section 4.3 - Nondeterministic Computing
(include "/home/zv/z/practice/sicp/4/amb-evaluator.scm")

(define (amb/install-procedure p)
  (put dispatch-tt 'amb (car p) (cadr p)))

(map amb/install-procedure
     `([amb    ,amb/analyze-amb]
       [set!   ,amb/analyze-assignment]
       [define ,amb/analyze-definition]
       [if     ,amb/analyze-if]
       [lambda ,amb/analyze-lambda]
       [begin  ,(λ (exp) (amb/analyze-sequence (begin-actions exp)))]
       [cond   ,(λ (exp) (amb/analyze (cond->if exp)))]))

(install-driver-loop 'amb amb/driver-loop)

(amb/install-procedure `(let ,(λ (exp) (amb/analyze (let->combination exp)))))

(define amb/infuse-exprs '())
(define (amb/infuse exp)
  "This runs an expression to be 'infused' (e.g: define) into the environment at
a later callsite"
  (set! amb/infuse-exprs (cons exp amb/infuse-exprs)))

(define (amb/execute-infuse-expressions env)
  "Actually begin evaluating the expressionss added to `infuse-exprs'"
  (map (λ (e)
         (ambeval e env
                  ;; success
                  (λ (_value _next-alternative) #t)
                  ;; failure
                  (λ () (error "INFUSE: " env))))
       amb/infuse-exprs))

;; A logic programming 'requirement'
(amb/infuse
 '(define (require p) (if (not p) (amb))))

(amb/infuse
 '(define (an-integer-starting-from n)
    (amb n (an-integer-starting-from (+ n 1)))))


;; Required to implement several
(amb/infuse
 '(define (distinct? items)
    (cond ((null? items) true)
          ((null? (cdr items)) true)
          ((member (car items) (cdr items)) false)
          (else (distinct? (cdr items))))))

(include "/home/zv/z/practice/sicp/4/eval-driver.scm")
(define the-global-environment (setup-environment))
(if inside-repl? 'ready ;; we want the repl available ASAP if were inside emacs
    (begin
      ;; load our tests
      (load "test/evaluator.scm")
      ;; start the REPL
      (driver-loop 'amb)))
