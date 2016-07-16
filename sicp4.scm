;;; -*- mode: scheme; coding: utf-8; -*-
(use-modules (ice-9 q))
(use-modules (ice-9 format))
(use-modules (ice-9 pretty-print))
(use-modules (ice-9 match))
(use-modules (oop goops))
(use-modules (srfi srfi-1))

(define (inc a) (+ a 1))
(define (curry fn . c-args)
  (λ args
    (apply fn (append c-args args))))


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

(define (zeval. exp env)
  (cond [(self-evaluating? exp)
         exp]
        [(variable? exp)
         (lookup-variable-value exp env)]
        [(quoted? exp)
         (text-of-quotation exp)]
        [(assignment? exp)
         (eval-assignment exp env)]
        [(definition? exp)
         (eval-definition exp env)]
        [(if? exp)
         (eval-if exp env)]
        [(lambda? exp)
         (make-procedure
          (lambda-parameters exp)
          (lambda-body exp)
          env)]
        [(begin? exp)
         (eval-sequence
          (begin-actions exp)
          env)]
        [(cond? exp)
         (zeval (cond->if exp) env)]
        [(application? exp)
         (zapply (zeval (operator exp) env)
                 (list-of-values
                  (operands exp)
                  env))]
        (else
         (error "Unknown expression type: EVAL" exp))))


(define (zapply procedure arguments)
  "Apply takes two arguments, a procedure and a list of arguments to which the
procedure should be applied. Apply classifies procedures into two kinds: It
calls apply-primitive-procedure to apply primitives; it applies compound
procedures by sequentially evaluating the expressions that make up the body of
the procedure. The environment for the evaluation of the body of a compound
procedure is constructed by extending the base environment carried by the
procedure to include a frame that binds the parameters of the procedure to the
arguments to which the procedure is to be applied. Here is the definition of
apply"
  (cond ((primitive-procedure? procedure)
         (apply-primitive-procedure
          procedure
          arguments))
        ((compound-procedure? procedure)
         (eval-sequence
          (procedure-body procedure)
          (extend-environment
           (procedure-parameters procedure)
           arguments
           (procedure-environment procedure))))
        (else
         (error "Unknown procedure
                 type: APPLY"
                procedure))))



                                        ; Procedure arguments

;; When eval processes a procedure application, it uses list-of-values to
;; produce the list of arguments to which the procedure is to be applied.
;; List-of-values takes as an argument the operands of the combination. It
;; evaluates each operand and returns a list of the corresponding values:209

(define (list-of-values exps env)
  (if (no-operands? exps)
      '()
      (cons (zeval (first-operand exps) env)
            (list-of-values
             (rest-operands exps)
             env))))


                                        ; Conditionals

(define (eval-if exp env)
  "Eval-if evaluates the predicate part of an if expression in the given
environment. If the result is true, eval-if evaluates the consequent, otherwise
it evaluates the alternative:"
  (if (true? (zeval (if-predicate exp) env))
      (zeval (if-consequent exp) env)
      (zeval (if-alternative exp) env)))


(define (eval-sequence exps env)
  "Eval-sequence is used by apply to evaluate the sequence of expressions in a
procedure body and by eval to evaluate the sequence of expressions in a begin
expression. It takes as arguments a sequence of expressions and an environment,
and evaluates the expressions in the order in which they occur. The value
returned is the value of the final expression."
  (cond ((last-exp? exps)
         (zeval (first-exp exps) env))
        (else
         (zeval (first-exp exps) env)
         (eval-sequence (rest-exps exps)
                        env))))


                                        ; Assignments and definitions


(define (eval-assignment exp env)
  "handles assignments to variables. It calls eval to find the value to be
assigned and transmits the variable and the resulting value to
set-variable-value! to be installed in the designated environment."
  (set-variable-value!
   (assignment-variable exp)
   (zeval (assignment-value exp) env)
   env)
  'ok)

;; Definitions of variables are handled in a similar manner.

(define (eval-definition exp env)
  (define-variable!
    (definition-variable exp)
    (zeval (definition-value exp) env)
    env)
  'ok)


                                        ; Syntax Specification

;; The only self-evaluating items are numbers and strings:
(define (self-evaluating? exp)
  (cond ((number? exp) #t)
        ((string? exp) #t)
        (else #f)))

;; Variables are represented by symbols:
(define (variable? exp) (symbol? exp))

;; Quotations have the form (quote ⟨text-of-quotation⟩)
(define (quoted? exp)
  (tagged-list? exp 'quote))

(define (text-of-quotation exp)
  (cadr exp))

;; Quoted? is defined in terms of the procedure tagged-list?, which identifies lists beginning with a designated symbol:
(define (tagged-list? exp tag)
  (if (pair? exp)
      (eq? (car exp) tag)
      #f))

(define (assignment? exp) (tagged-list? exp 'set!))
(define (assignment-variable exp) (cadr exp))
(define (assignment-value exp) (caddr exp))
(define (definition? exp) (tagged-list? exp 'define))

(define (definition-variable exp)
  (if (symbol? (cadr exp))
      (cadr exp)
      (caadr exp)))

(define (definition-value exp)
  (if (symbol? (cadr exp))
      (caddr exp)
      (make-lambda
       (cdadr exp)   ; formal parameters
       (cddr exp)))) ; body

;; Lambda expressions are lists that begin with the symbol lambda:
(define (lambda? exp)
  (tagged-list? exp 'lambda))
(define (lambda-parameters exp) (cadr exp))
(define (lambda-body exp) (cddr exp))

;; We also provide a constructor for lambda expressions, which is used by definition-value, above:
(define (make-lambda parameters body)
  (cons 'lambda (cons parameters body)))

;; Conditionals begin with if and have a predicate, a consequent, and an
;; (optional) alternative. If the expression has no alternative part, we provide
;; false as the alternative.214
(define (if? exp) (tagged-list? exp 'if))
(define (if-predicate exp) (cadr exp))
(define (if-consequent exp) (caddr exp))
(define (if-alternative exp)
  (if (not (null? (cdddr exp)))
      (cadddr exp)
      'false))

;; We also provide a constructor for if expressions, to be used by cond->if to
;; transform cond expressions into if expressions:
(define (make-if predicate consequent alternative)
  (list 'if
        predicate
        consequent
        alternative))

;; Begin packages a sequence of expressions into a single expression. We include
;; syntax operations on begin expressions to extract the actual sequence from the
;; begin expression, as well as selectors that return the first expression and the
;; rest of the expressions in the sequence.
(define (begin? exp)
  (tagged-list? exp 'begin))
(define (begin-actions exp) (cdr exp))
(define (last-exp? seq) (null? (cdr seq)))
(define (first-exp seq) (car seq))
(define (rest-exps seq) (cdr seq))

;; We also include a constructor sequence->exp (for use by cond->if) that
;; transforms a sequence into a single expression, using begin if necessary:
(define (sequence->exp seq)
  (cond ((null? seq) seq)
        ((last-exp? seq) (first-exp seq))
        (else (make-begin seq))))

(define (make-begin seq) (cons 'begin seq))

;; A procedure application is any compound expression that is not one of the
;; above expression types. The car of the expression is the operator, and the cdr
;; is the list of operands:
(define (application? exp) (pair? exp))
(define (operator exp) (car exp))
(define (operands exp) (cdr exp))
(define (no-operands? ops) (null? ops))
(define (first-operand ops) (car ops))
(define (rest-operands ops) (cdr ops))

(define (cond? exp)
  (tagged-list? exp 'cond))
(define (cond-clauses exp) (cdr exp))
(define (cond-else-clause? clause)
  (eq? (cond-predicate clause) 'else))
(define (cond-predicate clause)
  (car clause))
(define (cond-actions clause)
  (cdr clause))
(define (cond->if exp)
  (expand-clauses (cond-clauses exp)))
(define (expand-clauses clauses)
  (if (null? clauses)
      'false     ; no else clause
      (let ((first (car clauses))
            (rest (cdr clauses)))
        (if (cond-else-clause? first)
            (if (null? rest)
                (sequence->exp
                 (cond-actions first))
                (error "ELSE clause isn't
                        last: COND->IF"
                       clauses))
            (make-if (cond-predicate first)
                     (sequence->exp
                      (cond-actions first))
                     (expand-clauses
                      rest))))))



                                        ; Evaluator Data Structures
(define (true? x)
  (not (eq? x #f)))

(define (false? x)
  (eq? x #f))

(define (make-procedure parameters body env)
  (list 'procedure parameters body env))
(define (compound-procedure? p)
  (tagged-list? p 'procedure))
(define (procedure-parameters p) (cadr p))
(define (procedure-body p) (caddr p))
(define (procedure-environment p) (cadddr p))

(define (enclosing-environment env) (cdr env))
(define (first-frame env) (car env))
(define the-empty-environment '())

;; Each (stack) frame of an environment is represented as a pair of lists: a list of the
;; variables bound in that frame and a list of the associated values.
;; Each frame of an environment is represented as a pair of lists: a list of the
;; variables bound in that frame and a list of the associated values.
#|
(define (make-frame variables values)
  (cons variables values))
|#
(define (frame-variables frame) (car frame))
(define (frame-values frame) (cdr frame))
(define (add-binding-to-frame! var val frame)
  (set-car! frame (cons var (car frame)))
  (set-cdr! frame (cons val (cdr frame))))

(define (extend-environment vars vals base-env)
  "To extend an environment by a new frame that associates variables with
values, we make a frame consisting of the list of variables and the list of
values, and we adjoin this to the environment. We signal an error if the number
of variables does not match the number of values."
  (if (= (length vars) (length vals))
      (cons (make-frame vars vals) base-env)
      (if (< (length vars) (length vals))
          (error "Too many arguments supplied" vars vals)
          (error "Too few arguments supplied" vars vals))))

(define (lookup-variable-value var env)
  "To look up a variable in an environment, we scan the list of variables in the
first frame. If we find the desired variable, we return the corresponding
element in the list of values. If we do not find the variable in the current
frame, we search the enclosing environment, and so on. If we reach the empty
environment, we signal an “unbound variable” error."
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop
              (enclosing-environment env)))
            ((eq? var (car vars))
             (car vals))
            (else (scan (cdr vars)
                        (cdr vals)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable" var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))


(define (set-variable-value! var val env)
  "To set a variable to a new value in a specified environment, we scan for the
variable, just as in lookup-variable-value, and change the corresponding value
when we find it."
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop
              (enclosing-environment env)))
            ((eq? var (car vars))
             (set-car! vals val))
            (else (scan (cdr vars)
                        (cdr vals)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable: SET!" var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))


(define (define-variable! var val env)
  "To define a variable, we search the first frame for a binding for the
variable, and change the binding if it exists (just as in set-variable-value!).
If no such binding exists, we adjoin one to the first frame."
  (let ((frame (first-frame env)))
    (define (scan vars vals)
      (cond ((null? vars)
             (add-binding-to-frame!
              var val frame))
            ((eq? var (car vars))
             (set-car! vals val))
            (else (scan (cdr vars)
                        (cdr vals)))))
    (scan (frame-variables frame)
          (frame-values frame))))


(define (primitive-procedure? proc)
  (tagged-list? proc 'primitive))

(define (primitive-implementation proc)
  (cadr proc))

(define primitive-procedures
  (list (list 'car car)
        (list 'cdr cdr)
        (list 'cons cons)
        (list 'null? null?)))

(define (primitive-procedure-names)
  (map car primitive-procedures))

(define (primitive-procedure-objects)
  (map (lambda (proc)
         (list 'primitive (cadr proc)))
       primitive-procedures))


(define (apply-primitive-procedure proc args)
  "To apply a primitive procedure, we simply apply the implementation procedure
to the arguments, using the underlying Lisp system"
  (apply
   (primitive-implementation proc) args))

(define (setup-environment)
  (let ((initial-env
         (extend-environment
          (primitive-procedure-names)
          (primitive-procedure-objects)
          the-empty-environment)))
    (define-variable! 'true #t initial-env)
    (define-variable! 'false #f initial-env)
    initial-env))


                                        ; Driver Functions

;;; For convenience in running the metacircular evaluator, we provide a driver
;;; loop that models the read-eval-print loop of the underlying Lisp system. It
;;; prints a prompt, reads an input expression, evaluates this expression in the
;;; global environment, and prints the result. We precede each printed result by an
;;; output prompt so as to distinguish the value of the expression from other output
;;; that may be printed.

(define input-prompt  ";;; M-Eval input:")
(define output-prompt ";;; M-Eval value:")

(define (user-print object)
  (if (compound-procedure? object)
      (display
       (list 'compound-procedure
             (procedure-parameters object)
             (procedure-body object)
             '<procedure-env>))
      (display object)))

(define (driver-loop)
  (prompt-for-input input-prompt)
  (let ((input (read)))
    (let ((output
           (zeval input
                  the-global-environment)))
      (announce-output output-prompt)
      (user-print output)))
  (driver-loop))

(define (prompt-for-input string)
  (newline) (newline)
  (display string) (newline))

(define (announce-output string)
  (newline) (display string) (newline))


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
         ,body)))))

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
                                          (pretty-print environment)
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

((lambda () (define a 1) (define b 2) (cons a b)))
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
  (if (null? expr) 'false
      (%as-syntax
       (let
           ,(map ; generate the (binding . '*unassigned) let binds
             (λ (v) (list v '*unassigned))
             (map car (cadr expr)))

         ,@(map ; generate the `set!' expressions
            (λ (bind) `(set! ,(car bind) ,(cadr bind)))
            (let-bindings expr))

         ;; and merge our existing body
         ,@(let-body expr)))))

(test-equal
    (letrec->let
     `(let ((a (lambda () (b)))
            (b (lambda () (a))))
        (x a)
        (x b)
        (x c)))

  '(let ((a *unassigned)
         (b *unassigned))
     (set! a (lambda () (b)))
     (set! b (lambda () (a)))
     (x a)
     (x b)
     (x c)))

;; 2.
;; The main problem with Louis's reasoning is that the environment that `let' is
;; being evaluating against is actually expressed in the form of a `lambda' whoses
;; actual function bodies are being passed in as arguments (in the case of (f x)),
;; this means that the lexical scope of `even?' cannot see that of `odd?' and
;; versa.

;; Section 4.2


(define the-global-environment (setup-environment))
(driver-loop)
