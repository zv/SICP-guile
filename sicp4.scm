;;; -*- mode: scheme; coding: utf-8; -*-
(use-modules (ice-9 format))
(use-modules (ice-9 q))
(use-modules (oop goops))


(define (inc n) (+ n 1))
(define (dec n) (- n 1))



;; Custom Macros
(define-syntax generate-accessors
  (syntax-rules (generate-accessors define exp)
    ((generate-accessors ()) #t)

    ((generate-accessors ((fn def) . remaining))
     (begin
       (define (fn exp) (def exp))
       (generate-accessors remaining)))

    ((generate-accessors non-list)
     (syntax-error "not a list"))))


;; Section 4.1

(define (zeval. exp env)
  (cond [(self-evaluating? exp)
         exp]
        [(variable? exp)
         (lookup-variable-value exp env)]
        ((or? exp)
         (eval-or exp env))
        ((and? exp)
         (eval-and exp env))
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
             (procedure-parameters
              procedure)
             arguments
             (procedure-environment
              procedure))))
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

;; Conditionals begin with if and have a predicate, a consequent, and an (optional) alternative. If the expression has no alternative part, we provide false as the alternative.214
(define (if? exp) (tagged-list? exp 'if))
(define (if-predicate exp) (cadr exp))
(define (if-consequent exp) (caddr exp))
(define (if-alternative exp)
  (if (not (null? (cdddr exp)))
      (cadddr exp)
      'false))

;; We also provide a constructor for if expressions, to be used by cond->if to transform cond expressions into if expressions:
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

;; We also include a constructor sequence->exp (for use by cond->if) that transforms a sequence into a single expression, using begin if necessary:
(define (sequence->exp seq)
  (cond ((null? seq) seq)
        ((last-exp? seq) (first-exp seq))
        (else (make-begin seq))))

(define (make-begin seq) (cons 'begin seq))

;; A procedure application is any compound expression that is not one of the above expression types. The car of the expression is the operator, and the cdr is the list of operands:
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

(define (make-frame variables values)
  (cons variables values))
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
          (error "Too many arguments supplied"
                 vars
                 vals)
          (error "Too few arguments supplied"
                 vars
                 vals))))

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
          (frame-values frame))))(define (enclosing-environment env) (cdr env))
(define (first-frame env) (car env))
(define the-empty-environment '())

;; Each frame of an environment is represented as a pair of lists: a list of the
;; variables bound in that frame and a list of the associated values.
(define (make-frame variables values)
  (cons variables values))
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

(define the-global-environment
  (setup-environment))


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
   [set    ,eval-assignment]
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
 ([let-bindings cadr]
  [let-body     cddr]
  [let-binding-vars  (λ (b) (map car b))]
  [let-binding-exprs (λ (b) (map cadr b))]))

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
 ([let*-body caddr]
  [let*-inits cadr]))

#|
(define (let*->nested-let exp)
  (define (next exp)
    (list (operator exp) (cdadr exp) (caddr exp)))
  (if (null? exp) 'false
      (let ([bindings (let-bindings exp)]
            [body     (let-body exp)])
        (if (null? bindings) body
            (make-let->lambda
             (list (car (let-binding-vars bindings)))
             (list (car (let-binding-exprs bindings)))
             (let*->nested-let (next exp)))))))
|#

(define (let*->nested-lets expr)
  (let ([inits (let*-inits expr)]
        [body (let*-body expr)])
    (define (next expr)
      (if (null? expr) body
          (list 'let (list (car expr)) (next (cdr expr)))))
    (next inits)))


(install-procedure `(let* ,(λ (exp env) (zeval (let*->nested-lets exp) env))))
(driver-loop)
