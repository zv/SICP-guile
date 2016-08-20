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

(test-begin "Lazy Evaluator")

;; initialize
(define test-environment (setup-environment))
(define test-evaluator leval)

;; ;; analyzer tests
;; (test-eval 1 => 1)
;; (test-eval (define definet 1) => 'ok)
;; (test-eval definet => 1)
;; (test-eval (if (= 1 2) false true) => #t)
;; (test-eval
;;  (define (try a b) (if (= a 0) 1 b))
;;  => 'ok)

;; (test-eval (try 0 (/ 1 0)) => 1)

;; (test-eval
;;  (cond
;;   ((= 1 2) 0)
;;   ((= (+ 1 1) 3) 0)
;;   (else 1))
;;  => 1)

(test-end "Lazy Evaluator")

(test-begin "amb Evaluator")
(define test-environment (setup-environment))
(amb/execute-infuse-expressions test-environment)

(define (amb/test-amb expr)
  (ambeval expr test-environment
           ;; success
           (λ (value next-alternative)
             (cons value (next-alternative)))
           ;; failure
           (λ ()
             ;; no more values
             '())))

(define (amb/test-evaluator expr)
  (ambeval expr test-environment
           (λ (value _next-alternative) value)
           (λ () (error "no values"))))

(define-syntax test-amb
  (syntax-rules (=> test-environment test-equal)
    ((test-eval expr =>)
     (syntax-error "no expect statement"))
    ((test-eval expr => expect)
     (test-assert
         (equal?
          (amb/test-evaluator 'expr)
          expect)))
    ((test-eval expr expect)
     (test-eqv expect (amb/test-evaluator 'expr)))
    ((test-eval expr &~> expect)
     (test-assert
         (equal?
          (amb/test-amb 'expr)
          expect)))))


(test-amb (if (< 1 2) true false) => #t)
(test-amb (amb 1 2 3) &~> '(1 2 3))

(test-begin "Sentence Puzzles")
;; These are test cases from SICP proper
(test-amb (parse '(the cat eats))
          => '(sentence (simple-noun-phrase (article the) (noun cat)) (verb eats)))

(test-amb (parse '(the student with the cat sleeps in the class))
          => '(sentence
               (noun-phrase
                (simple-noun-phrase (article the) (noun student))
                (prep-phrase
                 (prep with)
                 (simple-noun-phrase
                  (article the)
                  (noun cat))))
               (verb-phrase
                (verb sleeps)
                (prep-phrase
                 (prep in)
                 (simple-noun-phrase (article the) (noun class))))))

(test-amb (parse '(the professor lectures to the student with the cat))
          &~> '(
                (sentence
                 (simple-noun-phrase (article the) (noun professor))
                 (verb-phrase
                  (verb-phrase
                   (verb lectures)
                   (prep-phrase (prep to)
                                (simple-noun-phrase
                                 (article the)
                                 (noun student))))
                  (prep-phrase (prep with)
                               (simple-noun-phrase
                                (article the)
                                (noun cat)))))
                ;; next
                (sentence
                 (simple-noun-phrase (article the) (noun professor))
                 (verb-phrase
                  (verb lectures)
                  (prep-phrase (prep to)
                               (noun-phrase
                                (simple-noun-phrase
                                 (article the) (noun student))
                                (prep-phrase (prep with)
                                             (simple-noun-phrase
                                              (article the)
                                              (noun cat)))))))
                ))

(test-end "Sentence Puzzles")



(test-end "amb Evaluator")


(test-end "Evaluator")

(test-end "Tests")
