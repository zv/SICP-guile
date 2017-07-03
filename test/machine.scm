;; -*- mode: scheme; fill-column: 75; comment-column: 50; coding: utf-8; geiser-scheme-implementation: guile -*-

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
;;                              (jeq (label gcd-done)) ;; conditional branch
;;                              (t<-r)                    ;; button push
;;                              (a<-b)                    ;; button push
;;                              (b<-t)                    ;; button push
;;                              (goto (label test-b))     ;; unconditional branch
;;                              gcd-done))

;; (define-register-machine test-gcd
;;   #:assembly (test-b
;;               (test (op =) (reg b) (const 0))
;;               (jeq (label gcd-done))
;;               (movw t (reg a))
;;               rem-loop
;;               (test (op <) (reg t) (reg b))
;;               (jeq (label rem-done))
;;               (movw t (op -) (reg t) (reg b))
;;               (goto (label rem-loop))
;;               rem-done
;;               (movw a (reg b))
;;               (movw b (reg t))
;;               (goto (label test-b))
;;               gcd-done))

;; (define-register-machine recursive-gcd
;;   #:assembly
;;   (movw continue (label fact-done))   ; set up final return address fact-loop
;;   (test (op =) (reg n) (const 1))
;;   (jeq (label base-case))
;;   (push continue)                       ; Set up for the recursive call
;;   (push n)                              ; by saving n and continue.
;;   (movw n (op -) (reg n) (const 1))   ; Set up continue so that the
;;   (movw continue (label after-fact))  ; computation will continue
;;   (goto (label fact-loop))              ; at after-fact when the after-fact                              ; subroutine returns.
;;   (pop n)
;;   (pop continue)
;;   (movw val (op *) (reg n) (reg val)) ; val now contains n(n - 1)!
;;   (goto (reg continue))                 ; return to caller base-case
;;   (movw val (const 1))                ; base case: 1! = 1
;;   (goto (reg continue)))                 ; return to caller fact-done)

;; (test-equal 720 (get-register-contents factorial 'product))
;; (test-approximate 9 (get-register-contents newtons 'guess))

(test-end "register simulator")

(define sample-text '((movw counter (const 1))
                      (movw product (const 1))
                      loop
                      (push 1)
                      (pop counter)
                      (pop counter)
                      (test (op >) (reg counter) (reg n))
                      (jeq (label end-fib))
                      (movw product (op *) (reg counter) (reg product))
                      (movw counter (op +) (reg counter) (const 1))
                      (goto (label loop))
                      end-fib))


(test-equal
    '(1 counter)
    (extract-stack-manipulations sample-text))

(test-equal
    '(loop)
    (extract-goto-destinations sample-text))

(test-begin "register helper fns")

(test-end "register helper fns")

(test-end "tests")
