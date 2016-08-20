(define (leval expr env)
  (let ([dispatch-fn (get dispatch-tt 'leval (list-tag expr))])
    (cond
     [(self-evaluating? expr) expr]
     [(variable? expr)
      (lookup-variable-value expr env)]
     [(procedure? dispatch-fn)
      (dispatch-fn expr env)]
     [(application? expr)
      (lapply (actual-value (operator expr) env)
              (operands expr) env)]
     [else (error "Bad Expression" expr)])))

(define (lapply procedure arguments env)
  (cond ((primitive-procedure? procedure)
         (apply-primitive-procedure
          procedure
          (list-of-arg-values arguments env)))  ; changed
        ((compound-procedure? procedure)
         (leval-sequence
          (procedure-body procedure)
          (extend-environment
           (procedure-parameters procedure)
           (list-of-delayed-args arguments env)   ; changed
           (procedure-environment procedure))))
        (else (error "Unknown procedure type: APPLY"
                     procedure))))

#|
The procedures that process the arguments are just like list-of-values from
4.1.1, except that list-of-delayed-args delays the arguments instead of
evaluating them, and list-of-arg-values uses actual-value instead of eval:
|#

(define (list-of-arg-values exps env)
  (if (no-operands? exps)
      '()
      (cons (actual-value
             (first-operand exps)
             env)
            (list-of-arg-values
             (rest-operands exps)
             env))))

(define (list-of-delayed-args exps env)
  (if (no-operands? exps) '()
      (cons (delay-it (first-operand exps) env)
            (list-of-delayed-args (rest-operands exps) env))))

;; Laziness Datastfuctures
(define (actual-value exp env)
  "Force the lazy value"
  (force-it (leval exp env)))

(define (force-it obj)
  "To force the thunk, we simply extract the expression and environment from the
thunk and evaluate the expression in the environment."
  (if (thunk? obj)
      (actual-value (thunk-exp obj)
                    (thunk-env obj))
      obj))

(define (delay-it exp env)
  (list 'thunk exp env))
(define (thunk? obj) (tagged-list? obj 'thunk))
(define (thunk-exp thunk) (cadr thunk))
(define (thunk-env thunk) (caddr thunk))

(define (evaluated-thunk? obj)
  (tagged-list? obj 'evaluated-thunk))

(define (thunk-value evaluated-thunk)
  (cadr evaluated-thunk))

(define (force-it obj)
  "This is just a memoizing version of `force-it'"
  (cond ((thunk? obj)
         (let ((result
                (actual-value
                 (thunk-exp obj)
                 (thunk-env obj))))
           (set-car! obj 'evaluated-thunk)
           ;; replace exp with its value:
           (set-car! (cdr obj) result)
           ;; forget unneeded env:
           (set-cdr! (cdr obj) '())
           result))
        ((evaluated-thunk? obj)
         (thunk-value obj))
        (else obj)))


;; Procedures

(define (leval-if exp env)
  "The other place we must change the evaluator is in the handling of if, where
we must use actual-value instead of eval to get the value of the predicate
expression before testing whether it is true or false: "
  (if (true? (actual-value (if-predicate exp)
                           env))
      (leval (if-consequent exp) env)
      (leval (if-alternative exp) env)))

(define (leval-assignment exp env)
  "handles assignments to variables. It calls eval to find the value to be
assigned and transmits the variable and the resulting value to
set-variable-value! to be installed in the designated environment."
  (set-variable-value!
   (assignment-variable exp)
   (leval (assignment-value exp) env)
   env)
  'ok)

(define (leval-definition exp env)
  (define-variable!
    (definition-variable exp)
    (leval (definition-value exp) env)
    env)
  'ok)

(define (leval-sequence exps env)
  (cond ((last-exp? exps)
         (leval (first-exp exps) env))
        (else
         (leval (first-exp exps) env)
         (leval-sequence (rest-exps exps)
                        env))))

;; Install our procedures
(define (install-lazy-procedure p) (put dispatch-tt 'leval (car p) (cadr p)))
(map
 install-lazy-procedure
 `([quote  ,(λ (expr env) (text-of-quotation expr))]
   [set!    ,leval-assignment]
   [define ,leval-definition]
   [if     ,leval-if]
   [lambda ,(λ (expr env) (make-procedure (lambda-parameters expr) (lambda-body expr) env))]
   [begin  ,(λ (expr env) (leval-sequence (begin-actions expr) env))]
   [cond   ,(λ (expr env) (leval (cond->if expr) env))]))
