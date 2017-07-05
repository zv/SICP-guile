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



(define* (test-machine name machine #:key arguments expected)
  (define (set-registers registers)
    (map (λ (elt)
           (if (list? elt)
               (set-register-contents! machine (car elt) (cadr elt))))
         registers))

  (define (test-result results)
    (map
     (λ (elt)
       (test-equal name (cadr elt) (get-register-contents machine (car elt))))
     results))

  (set-registers arguments)
  (machine 'start)
  (test-result expected))

(test-begin "tests")
(test-begin "register simulator")

;; Exercise 5.1
(test-machine "factorial"
              factorial
              #:arguments '((n 6))
              #:expected '((product 720)))


;; Exercise 5.3
(test-machine "newtons"
              newtons
              #:arguments '((x 64))
              #:expected '((guess 8.000001655289593)))


;; Exercise 5.4
(test-machine "recursive-expt"
              recursive-expt
              #:arguments '((b 10) (n 2))
              #:expected '((product 100)))

(test-machine "iter-expt"
              iter-expt
              #:arguments '((b 10) (n 2))
              #:expected '((product 100)))


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


(test-equal '(1 counter) (extract-stack-manipulations sample-text))
(test-equal '(loop) (extract-goto-destinations sample-text))

(test-begin "register helper fns")

(test-end "register helper fns")

(test-end "tests")
