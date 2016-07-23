(define (analyze exp)
  "The procedure analyze takes only the expression. It performs the syntactic
analysis and returns a new procedure, the execution procedure, that encapsulates
the work to be done in executing the analyzed expression. The execution
procedure takes an environment as its argument and completes the evaluation.
This saves work because analyze will be called only once on an expression, while
the execution procedure may be called many times."
  (cond ((self-evaluating? exp)
         (analyze-self-evaluating exp))
        ((quoted? exp)
         (analyze-quoted exp))
        ((variable? exp)
         (analyze-variable exp))
        ((assignment? exp)
         (analyze-assignment exp))
        ((definition? exp)
         (analyze-definition exp))
        ((if? exp)
         (analyze-if exp))
        ((lambda? exp)
         (analyze-lambda exp))
        ((begin? exp)
         (analyze-sequence
          (begin-actions exp)))
        ((cond? exp)
         (analyze (cond->if exp)))
        ((application? exp)
         (analyze-application exp))
        (else
         (error "Unknown expression type: ANALYZE" exp))))

(define (analyze-self-evaluating exp)
  "It returns an execution procedure that ignores its environment argument and
just returns the expression:"
  (lambda (env) exp))

(define (analyze-quoted exp)
  "For a quoted expression, we can gain a little efficiency by extracting the
text of the quotation only once, in the analysis phase, rather than in the
execution phase."
  (let ((qval (text-of-quotation exp)))
    (lambda (env) qval)))

(define (analyze-variable exp)
  "Looking up a variable value must still be done in the execution phase, since
this depends upon knowing the environment."
  (lambda (env)
    (lookup-variable-value exp env)))

(define (analyze-assignment exp)
  "analyze-assignment also must defer actually setting the variable until the
execution, when the environment has been supplied. However, the fact that the
assignment-value expression can be analyzed (recursively) during analysis is a
major gain in efficiency, because the assignment-value expression will now be
analyzed only once. The same holds true for definitions."
  (let ((var (assignment-variable exp))
        (vproc (analyze
                (assignment-value exp))))
    (lambda (env)
      (set-variable-value!
       var (vproc env) env)
      'ok)))

(define (analyze-definition exp)
  (let ((var (definition-variable exp))
        (vproc (analyze
                (definition-value exp))))
    (lambda (env)
      (define-variable! var (vproc env) env)
      'ok)))

(define (analyze-if exp)
  "For if expressions, we extract and analyze the predicate, consequent, and alternative at analysis time."
  (let ((pproc (analyze (if-predicate exp)))
        (cproc (analyze (if-consequent exp)))
        (aproc (analyze (if-alternative exp))))
    (lambda (env)
      (if (true? (pproc env))
          (cproc env)
          (aproc env)))))

(define (analyze-lambda exp)
  "Analyzing a lambda expression also achieves a major gain in efficiency: We
analyze the lambda body only once, even though procedures resulting from
evaluation of the lambda may be applied many times."
  (let ((vars (lambda-parameters exp))
        (bproc (analyze-sequence
                (lambda-body exp))))
    (lambda (env)
      (make-procedure vars bproc env))))


(define (analyze-sequence exps)
  "Analysis of a sequence of expressions (as in a begin or the body of a lambda
expression) is more involved.234 Each expression in the sequence is analyzed,
yielding an execution procedure. These execution procedures are combined to
produce an execution procedure that takes an environment as argument and
sequentially calls each individual execution procedure with the environment as
argument."
  (define (sequentially proc1 proc2)
    (lambda (env) (proc1 env) (proc2 env)))
  (define (loop first-proc rest-procs)
    (if (null? rest-procs)
        first-proc
        (loop (sequentially first-proc
                            (car rest-procs))
              (cdr rest-procs))))
  (let ((procs (map analyze exps)))
    (if (null? procs)
        (error "Empty sequence: ANALYZE"))
    (loop (car procs) (cdr procs))))


(define (analyze-application exp)
  "To analyze an application, we analyze the operator and operands and construct
an execution procedure that calls the operator execution procedure (to obtain
the actual procedure to be applied) and the operand execution procedures (to
obtain the actual arguments). We then pass these to execute-application, which
is the analog of apply in 4.1.1. Execute-application differs from apply in that
the procedure body for a compound procedure has already been analyzed, so there
is no need to do further analysis. Instead, we just call the execution procedure
for the body on the extended environment."
  (let ((fproc (analyze (operator exp)))
        (aprocs (map analyze (operands exp))))
    (lambda (env)
      (execute-application
       (fproc env)
       (map (lambda (aproc) (aproc env))
            aprocs)))))

(define (execute-application proc args)
  (cond ((primitive-procedure? proc)
         (apply-primitive-procedure proc args))
        ((compound-procedure? proc)
         ((procedure-body proc)
          (extend-environment
           (procedure-parameters proc)
           args
           (procedure-environment proc))))
        (else (error "Unknown procedure type:
                      EXECUTE-APPLICATION"
                     proc))))
