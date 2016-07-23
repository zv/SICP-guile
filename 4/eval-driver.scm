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

(define (prompt-for-input string)
  (newline) (newline)
  (display string) (newline))

(define (announce-output string)
  (newline) (display string) (newline))

(define (driver-loop evaluator)
  (prompt-for-input input-prompt)
  (let ((input (read)))
    (let ((output
           (evaluator input the-global-environment)))
      (announce-output output-prompt)
      (user-print output)))
  (driver-loop evaluator))


                                        ; Utility fns
(define (eval-+ exp env)
  (fold + 0 (map (λ (e) (zeval e env)) (operands exp))))

(define (eval-- exp env)
  (- (zeval (cadr exp) env)
     (zeval (caddr exp) env)))

(define (eval-= exp env)
  (=
   (zeval (car (operands exp)) env)
   (zeval (cadr (operands exp)) env)))

(install-procedure `(+ ,eval-+))
(install-procedure `(- ,eval--))
(install-procedure `(= ,eval-=))


                                        ; Analysis Utils
(define (analyze-+ exp)
  (λ (env) (eval-+ exp env)))

(define (analyze-- exp)
  (λ (env) (eval-- exp env)))

(define (analyze-= exp)
  (λ (env) (eval-= exp env)))

(install-analyze-procedure `(+ ,analyze-+))
(install-analyze-procedure `(- ,analyze--))
(install-analyze-procedure `(= ,analyze-=))
