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
  ((get dispatch-tt 'driver-loop evaluator)))

