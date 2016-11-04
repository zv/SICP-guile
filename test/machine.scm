(use-modules (srfi srfi-64))

(define (machine-sim-runner)
  (let* ((runner (test-runner-null))
         (num-passed 0)
         (num-failed 0))
    (test-runner-on-test-end! runner
      (lambda (runner)
        (case (test-result-kind runner)
          ((pass xpass) (set! num-passed (+ num-passed 1)))
          ((fail xfail)
           (begin
             (let
                 ((rez (test-result-alist runner)))
               (format #t
                       "~a::~a\n Expected Value: ~a | Actual Value: ~a\n Error: ~a\n Form: ~a\n"
                       (assoc-ref rez 'source-file)
                       (assoc-ref rez 'source-line)
                       (assoc-ref rez 'expected-value)
                       (assoc-ref rez 'actual-value)
                       (assoc-ref rez 'actual-error)
                       (assoc-ref rez 'source-form))
               (set! num-failed (+ num-failed 1)))))
          (else
           (format #t "something happened here\n")
           ))))
    (test-runner-on-final! runner
      (lambda (runner)
        (format #t "Passed: ~d || Failed: ~d.~%"
                num-passed num-failed)))
    runner))

(test-runner-factory
 (lambda () (machine-sim-runner)))



#|
(define* (machine-test name #:key result registers ops assembly)
  (define (register-names registers)
    (map (λ (elt)
           (if (list? elt) (car elt) elt))
         registers))

  (define (set-registers machine registers)
    (map (λ (elt)
           (if (list? elt)
               (set-register-contents! machine (car elt) (cadr elt))))
         registers))

  (define (test-result machine results)
    (map
     (λ (elt)
       (test-equal name (cadr elt) (get-register-contents machine (car elt))))
     results))

  (define mach (make-machine (register-names registers) ops assembly))

  (set-registers mach registers)
  (start mach)
  (test-result result))
|#

(test-begin "tests")
(test-begin "register simulator")

;; (test-machine "GCD"
;;               #:result     '((a 16))
;;               #:registers  '((a 120) (b 16) t)
;;               #:ops        `((rem ,modulo) (= ,=))
;;               #:assembly   '(test-b                    ;; label
;;                              (test =)                  ;; test
;;                              (branch (label gcd-done)) ;; conditional branch
;;                              (t<-r)                    ;; button push
;;                              (a<-b)                    ;; button push
;;                              (b<-t)                    ;; button push
;;                              (goto (label test-b))     ;; unconditional branch
;;                              gcd-done))


(define-register-machine test-gcd
  #:registers
  #:ops (= < -)
  #:assembly (test-b
   (test (op =) (reg b) (const 0))
   (branch (label gcd-done))
   (assign t (reg a))
   rem-loop
   (test (op <) (reg t) (reg b))
   (branch (label rem-done))
   (assign t (op -) (reg t) (reg b))
   (goto (label rem-loop))
   rem-done
   (assign a (reg b))
   (assign b (reg t))
   (goto (label test-b))
   gcd-done)
  )

(define-register-machine recursive-gcd
  #:registers (n val continue)
  #:ops (- * =)
  #:assembly (assign continue (label fact-done))   ; set up final return address fact-loop
                (test (op =) (reg n) (const 1))
                (branch (label base-case))
                (save continue)                       ; Set up for the recursive call
                (save n)                              ; by saving n and continue.
                (assign n (op -) (reg n) (const 1))   ; Set up continue so that the
                (assign continue (label after-fact))  ; computation will continue
                (goto (label fact-loop))              ; at after-fact when the after-fact                              ; subroutine returns.
                (restore n)   (restore continue)
                (assign val (op *) (reg n) (reg val)) ; val now contains n(n - 1)!
                (goto (reg continue))                 ; return to caller base-case
                (assign val (const 1))                ; base case: 1! = 1
                (goto (reg continue)))                 ; return to caller fact-done)

(test-equal (get-register-contents factorial 'product) 720)
(test-approximate (get-register-contents newtons 'guess) 9)

(test-end "register simulator")
(test-end "tests")
