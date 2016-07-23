(use-modules (srfi srfi-64))

; Standard Evaluator Tests
(define-syntax test-eval
  (syntax-rules (=> test-environment)
    ((test-eval expr =>)
     (syntax-error "no expect statement"))
    ((test-eval expr => expect)
     (test-assert (equal? (test-evaluator 'expr test-environment) expect)))
    ((test-eval expr expect)
     (test-assert (equal? (test-evaluator 'expr test-environment) expect)))))


(test-begin "test/4.0-evaluator")

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

;; cleanup
(set! test-environment '())
(test-end "test/4.0-evaluator")


(test-begin "test/4.1-analyzing-evaluator")

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

(test-end "test/4.1-analyzing-evaluator")
