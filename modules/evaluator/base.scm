(define-module (evaluator base)
  #:replace
  (zeval
   zapply list-of-values
   eval-if
   eval-sequence
   eval-assignment
   eval-definition
   self-evaluating?
   variable?
   quoted?
   text-of-quotation
   tagged-list?
   assignment?
   assignment-variable
   assignment-value
   definition?
   definition-variable
   definition-value
   lambda?
   lambda-parameters
   lambda-body
   make-lambda
   if?
   if-predicate
   if-consequent
   if-alternative
   make-if
   begin?
   begin-actions
   last-exp?
   first-exp
   rest-exps
   sequence->exp
   make-begin
   application?
   operator
   operands
   no-operands?
   first-operand
   rest-operands
   cond?
   cond-clauses
   cond-else-clause?
   cond-predicate
   cond-actions
   cond->if
   expand-clauses
   true?
   false?
   make-procedure
   compound-procedure?
   procedure-parameters
   procedure-body
   procedure-environment
   enclosing-environment
   first-frame
   make-frame
   frame-variables
   frame-values
   add-binding-to-frame!
   extend-environment
   lookup-variable-value
   set-variable-value!
   define-variable!
   primitive-procedure?
   primitive-implementation
   primitive-procedure-names
   primitive-procedure-objects
   apply-primitive-procedure
   the-empty-environment))

(define (zeval exp env)
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
