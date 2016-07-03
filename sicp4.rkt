#lang racket
(require (lib "trace.ss"))

(define (inc n) (+ n 1))
(define (dec n) (- n 1))

#| Utilities |#
(define (zv-eval expr env)
  "Eval takes as arguments an expression and an environment. It classifis the
expression and directs its evaluation. Eval is structured as a case analysis of
the syntactic type of the expression to be evaluated. In order to keep the
procedure general, we express the determination of the type of an expression
abstractly, making no commitment to any particular representation for the
various types of expressions. Each type of expression has a predicate that tests
for it and an abstract means for selecting its parts. This abstract syntax makes
it easy to see how we can change the syntax of the language by using the same
evaluator, but with a different collection of syntax procedures."
  (cond [(self-evaluating? expr)
         expr]
        [(variable? expr)
         (lookup-variable-value expr env)]
        [(quoted? expr)
         (text-of-quotation expr)]
        [(assignment? expr)
         (eval-assignment expr env)]
        [(definition? expr)
         (eval-definition expr env)]
        [(if? expr)
         (eval-if expr env)]
        [(procedure? expr)
         (make-procedure
          (lambda-parameters expr)
          (lambda-body expr)
          env)]
        [(begin? expr)
         (eval-sequence
          (begin-actions expr)
          env)]
        [(cond? expr)
         (zv-eval (cond->if expr) env)]
        [(application? expr)
         (apply (zv-eval (operator expr) env)
                (list-of-values
                 (operands expr)
                 env))]
        [else
         (error "Unknown expression
                 type: EVAL" expr)]))

;; Expression Components
(define (self-evaluating? expr)
  (cond ((number? expr) #t)
        ((string? expr) #t)
        (else #f)))

(define (variable? expr) (symbol? expr))

(define (quoted? expr)
  (tagged-list? expr 'quote))

(define (text-of-quotation expr)
  (cadr expr))

(define (tagged-list? expr tag)
  (if (pair? expr)
      (eq? (car expr) tag)
      false))

(define (assignment? expr)
  (tagged-list? expr 'set!))

(define (assignment-variable expr)
  (cadr expr))

(define (assignment-value expr) (caddr expr))
(define (definition? expr)
  (tagged-list? expr 'define))

(define (definition-variable expr)
  (if (symbol? (cadr expr))
      (cadr expr)
      (caadr expr)))

(define (definition-value expr)
  (if (symbol? (cadr expr))
      (caddr expr)
      (make-lambda
       (cdadr expr)   ; formal parameters
       (cddr expr)))) ; body

(define (lambda? expr)
  (tagged-list? expr 'lambda))
(define (lambda-parameters expr) (cadr expr))
(define (lambda-body expr) (cddr expr))

(define (make-lambda parameters body)
  (cons 'lambda (cons parameters body)))

(define (if? expr) (tagged-list? expr 'if))
(define (if-predicate expr) (cadr expr))
(define (if-consequent expr) (caddr expr))
(define (if-alternative expr)
  (if (not (null? (cdddr expr)))
      (cadddr expr)
      'false))

(define (begin? expr)
  (tagged-list? expr 'begin))
(define (begin-actions expr) (cdr expr))
(define (last-exp? seq) (null? (cdr seq)))
(define (first-exp seq) (car seq))
(define (rest-exps seq) (cdr seq))

(define (sequence->exp seq)
  (cond ((null? seq) seq)
        ((last-exp? seq) (first-exp seq))
        (else (make-begin seq))))

(define (make-begin seq) (cons 'begin seq))

(define (application? expr) (pair? expr))
(define (operator expr) (car expr))
(define (operands expr) (cdr expr))
(define (no-operands? ops) (null? ops))
(define (first-operand ops) (car ops))
(define (rest-operands ops) (cdr ops))

(define (lookup-variable-value var env)
  "To look up a variable in an environment, we scan the list of variables in the
first frame. If we find the desired variable, we return the corresponding
element in the list of values. If we do not find the variable in the current
frame, we search the enclosing environment, and so on. If we reach the empty
environment, we signal an “unbound variable” error. "
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

(define (make-procedure parameters body env)
  "Compound procedures are constructed from parameters, procedure bodies, and environments using the constructor make-procedure"
  (list 'procedure parameters body env))
(define (compound-procedure? p)
  (tagged-list? p 'procedure))
(define (procedure-parameters p) (cadr p))
(define (procedure-body p) (caddr p))
(define (procedure-environment p) (cadddr p))

;; We include syntax procedures that extract the parts of a cond expression, and
;; a procedure cond->if that transforms cond expressions into if expressions. A
;; case analysis begins with cond and has a list of predicate-action clauses. A
;; clause is an else clause if its predicate is the symbol else.
(define (cond? expr)
  (tagged-list? expr 'cond))
(define (cond-clauses expr) (cdr expr))
(define (cond-else-clause? clause)
  (eq? (cond-predicate clause) 'else))
(define (cond-predicate clause)
  (car clause))
(define (cond-actions clause)
  (cdr clause))
(define (cond->if expr)
  (expand-clauses (cond-clauses expr)))
(define (expand-clauses clauses)
  (if (null? clauses)
      'false     ; no else clause
      (let ((first (car clauses))
            (rest (cdr clauses)))
        (if (cond-else-clause? first)
            (if (null? rest)
                (sequence->exp (cond-actions first))
                (error "ELSE clause isn't last: COND->IF" clauses))
            (make-if (cond-predicate first)
                     (sequence->exp (cond-actions first))
                     (expand-clauses rest))))))


(define (apply procedure arguments)
  "Apply takes two arguments, a procedure and a list of arguments to which the
procedure should be applied. Apply classifies procedures into two kinds: It
calls apply-primitive-procedure to apply primitives; it applies compound
procedures by sequentially evaluating the expressions that make up the body of
the procedure. The environment for the evaluation of the body of a compound
procedure is constructed by extending the base environment carried by the
procedure to include a frame that binds the parameters of the procedure to the
arguments to which the procedure is to be applied. Here is the definition of
apply"
  (cond [(primitive-procedure? procedure)
         (apply-primitive-procedure procedure arguments)]
        [(compound-procedure? procedure)
         (eval-sequence
          (procedure-body procedure)
          (extend-environment
           (procedure-parameters procedure)
           arguments
           (procedure-environment procedure)))]
        [else
         (error "Unknown procedure type: APPLY"
                procedure)]))

(define (list-of-values exps env)
  "When zv-eval processes a procedure application, it uses list-of-values to
produce the list of arguments to which the procedure is to be applied.
List-of-values takes as an argument the operands of the combination. It
evaluates each operand and returns a list of the corresponding values:"
  (if (no-operands? exps)
      '()
      (cons (zv-eval (first-operand exps) env)
            (list-of-values
             (rest-operands exps)
             env))))

(define (eval-if expr env)
  "eval-if evaluates the predicate part of an if expression in the given
environment. If the result is true, eval-if evaluates the consequent, otherwise
it evaluates the alternative"
  (if (true? (zv-eval (if-predicate expr) env))
      (zv-eval (if-consequent expr) env)
      (zv-eval (if-alternative expr) env)))


(define (eval-sequence exps env)
  "Eval-sequence is used by apply to evaluate the sequence of expressions in a procedure body and by eval to evaluate the sequence of expressions in a begin expression. It takes as arguments a sequence of expressions and an environment, and evaluates the expressions in the order in which they occur. The value returned is the value of the final expression."
  (cond ((last-exp? exps)
         (zv-eval (first-exp exps) env))
        (else
         (zv-eval (first-exp exps) env)
         (eval-sequence (rest-exps exps)
                        env))))

(define (eval-assignment expr env)
  "This procedure handles assignments to variables. It calls zv-eval to find the
value to be assigned and transmits the variable and the resulting value to
set-variable-value! to be installed in the designated environment. "
  (set-variable-value!
   (assignment-variable expr)
   (zv-eval (assignment-value expr) env)
   env)
  'ok)

(define (eval-definition expr env)
  "Definitions of variables are handled in a similar manner."
  (define-variable!
    (definition-variable expr)
    (zv-eval (definition-value expr) env)
    env)
  'ok)

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
;; backwards.
(define (rtl-list-of-values exps env)
  (if (no-operands? exps)
      '()
      (let* ([left (zv-eval (first-operand exps) env)]
             [right (rtl-list-of-values (rest-operands exps) env)]))
      (cons left right)))

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
(factorial 3) we will now have to write (call factorial 3) and instead of (+ 1
2) we will have to write (call + 1 2). |#

#|Answer:
1: The order of operations will cause some variables to be undefined. As the
example suggests, define will be called with 'x' and '3' as arguments. `define'
cannot be made into a procedure because the arguments will be evaluated.

2. Only `application' need be changed:

    (define application? (exp)
      (tagged-list? exp 'call))
    (define operator (exp) (cadr exp))
    (define operands (exp) (cddr exp))

|#

#| Exercise 4.3
Rewrite eval so that the dispatch is done in data-directed style. Compare this
with the data-directed differentiation procedure of Exercise 2.73. (You may use
the car of a compound expression as the type of the expression, as is
appropriate for the syntax implemented in this section.) |#

(define dispatch-table%
  (class object%
    (define method-table (make-hash))

    (define/private (table-ordinal op type)
      (let ([opstr (symbol->string op)]
             [typestr (symbol->string type)])
             (string-append opstr "/" typestr)))

    (define/public (put op type item)
      (hash-set! method-table
                 (table-ordinal op type)
                 item))

    (define/public (get op type)
      (hash-ref method-table (table-ordinal op type)))))
