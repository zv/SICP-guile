(use-modules (srfi srfi-64))

(define (my-simple-runner)
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
          (else #t))))
    (test-runner-on-final! runner
      (lambda (runner)
        (format #t "Passed: ~d || Failed: ~d.~%"
                num-passed num-failed)))
    runner))

(test-runner-factory
 (lambda () (my-simple-runner)))

                                        ; Standard Evaluator Tests
(define-syntax test-eval
  (syntax-rules (=> test-environment test-equal)
    ((test-eval expr =>)
     (syntax-error "no expect statement"))
    ((test-eval expr => expect)
     (test-eqv  expect (test-evaluator 'expr test-environment)))
    ((test-eval expr expect)
     (test-eqv  expect (test-evaluator 'expr test-environment)))))

(test-begin "Tests")


(test-begin "Evaluator")

(test-begin "Basic")
;; initialize
(define test-environment (setup-environment))
(define test-evaluator zeval)

;; tests
(test-eval (or 1 2)                     => 1)
(test-eval (and 1 2)                    => 2)
(test-eval (begin 1 2)                  => 2)
(test-eval ((lambda (a b) (+ a b)) 3 4) => 7)
(test-eval (let ((a 1) (b 2)) a)        => 1)
(test-eval (let* ((a 1) (b 2) (c a)) c) => 1)

(test-eval
 (let fib-iter ((a 1) (b 0) (count 4))
   (if (= count 0) b
       (fib-iter (+ a b) a (- count 1))))
 => 3)

(test-eval
 (letrec ((sum (lambda (n) (if (= n 1) 1
                               (+ n (sum (- n 1)))))))
   (sum 2))
 => 3)

(test-eval
 (begin
   (define a 1)
   (define b 2)
   (set! a 3)
   (+ a b))
 => 5)

(test-eval
 (cond
  ((= 1 2) 0)
  ((= (+ 1 1) 3) 0)
  (else 1))
 => 1)

(test-eval
 (cond
  ((= 0 1) 0)
  ((= (+ 1 1) 2) 1)
  (else 0))
 => 1)

(test-eval
 (begin
   (define test (lambda (a) a))
   (test 1))
 => 1)

(test-eval (unless true 1 0) => 0)
(test-eval (unless false 1 0) => 1)

;; cleanup
(set! test-environment '())
(test-end "Basic")

(test-begin "Analyzer")

;; initialize
(define test-environment (setup-environment))
(define test-evaluator aeval)

;; analyzer tests
(test-eval (let ((a 1)) a)              => 1)
(test-eval (begin 1 2)                  => 2)
(test-eval ((lambda (a b) (+ a b)) 3 4) => 7)
(test-eval (let ((a 1) (b 2)) a)        => 1)

(test-eval
 (let fib-iter ((a 1) (b 0) (count 4))
   (if (= count 0) b
       (fib-iter (+ a b) a (- count 1))))
 => 3)

(test-eval
 (begin
   (define a 1)
   (define b 2)
   (set! a 3)
   (+ a b))
 => 5)

(test-eval
 (cond
  ((= 1 2) 0)
  ((= (+ 1 1) 3) 0)
  (else 1))
 => 1)

(test-eval
 (cond
  ((= 0 1) 0)
  ((= (+ 1 1) 2) 1)
  (else 0))
 => 1)

(test-eval
 (begin
   (define test (lambda (a) a))
   (test 1))
 => 1)

(test-eval (unless true 1 0) => 0)
(test-eval (unless false 1 0) => 1)

(test-end "Analyzer")

(test-end "Evaluator")

(test-end "Test")
