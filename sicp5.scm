;; -*- mode: scheme; fill-column: 75; comment-column: 50; coding: utf-8; geiser-scheme-implementation: guile -*-

#| Structure and Interpretation of Computer Programs - Chapter 5 |#

;; The Register Machine Simulation
(use-modules (ice-9 format))
(use-modules (ice-9 match))
(use-modules (ice-9 pretty-print))
;; (use-modules (oop goops))

(define inside-repl?
  ;; current-source-location is formatted in a line, column, filename alist
  ;; e.g ((line . INTEGER) (column . INTEGER) (filename . SYMBOL|FALSE))
  (eq? #f (assq-ref (current-source-location) 'filename)))

(define do-debug? #t)
(define (debug format-string . format-args)
  (if do-debug?
      (apply format `(#t
                      ,(string-append format-string "~&")
                      ,@format-args))))


;; Section 4.1
(include "/home/zv/z/practice/sicp/machine/register.scm")
(define (extract-config-names items)
  (map (lambda (elt)
         (if (list? elt)
             (car elt)
             elt))
       items))

(define* (build-rmachine #:key registers ops assembly)
  (let* ([register-names (extract-config-names registers)]
         [proc-ops (map (λ (op)
                     (if (list? op) op
                         (list op (eval op (interaction-environment)))))
                   ops)]
         [mach (make-machine register-names proc-ops assembly)])
    ;; Take each of the registers and set it's value as specified in the arguments
    (map (λ (elt)
           (if (list? elt)
               (set-register-contents! mach (car elt) (cadr elt))))
         registers)
    ;; done
    mach))

(define (machine-run mach init)
  "Run a machine with the registers initialized to the alist in `init' and
then dumps the values of all registers"
  (map (λ (el) (set-register-contents! mach (car el) (cdr el))) init)
  (start mach)
  (map
   (λ (reg) (cons (car reg)
                  (get-contents (get-register mach (car reg)))))
   (mach 'dump-registers)))

(define-syntax define-register-machine
  (syntax-rules ()
    ((define-register-machine var #:registers registers #:ops ops #:assembly assembly)
     (define var (build-rmachine
                  #:registers 'registers
                  #:ops       `ops
                  #:assembly  'assembly)))))


#| Exercise 5.1
Design a register machine to compute factorials using the iterative
algorithm specified by the following procedure. Draw data-path and
controller diagrams for this machine.

    (define (factorial n)
      (define (iter product counter)
        (if (> counter n)
            product
            (iter (* counter product)
                  (+ counter 1))))
      (iter 1 1))
|#

(define-register-machine factorial
  #:registers (n product counter)
  #:ops       (> * +)
  #:assembly  ((assign counter (const 1))
               (assign product (const 1))
               loop
               (test (op >) (reg counter) (reg n))
               (branch (label end-fib))
               (assign product (op *) (reg counter) (reg product))
               (assign counter (op +) (reg counter) (const 1))
               (goto (label loop))
               end-fib))


#| Exercise 5.3
Design a machine to compute square roots using Newton’s method, as
described in 1.1.7:

  (define (sqrt x)
    (define (good-enough? guess)
      (< (abs (- (square guess) x)) 0.001))
    (define (improve guess)
      (average guess (/ x guess)))
    (define (sqrt-iter guess)
      (if (good-enough? guess)
          guess
          (sqrt-iter (improve guess))))
    (sqrt-iter 1.0))

Begin by assuming that good-enough? and improve operations are available as
primitives. Then show how to expand these in terms of arithmetic
operations. Describe each version of the sqrt machine design by drawing a
data-path diagram and writing a controller definition in the
register-machine language.
|#

(define (average a b) (/ (+ a b) 2))
(define (square x) (* x x))
(define (newton/good-enough? guess x) (< (abs (- (square guess) x)) 0.001))
(define (newton/improve guess x) (average guess (/ x guess)))

(define-register-machine newtons
  #:registers (x guess)
  #:ops       ((good-enough ,newton/good-enough?)
               (improve ,newton/improve))
  #:assembly  ((assign guess (const 1.0))
               improve
               (test (op good-enough) (reg guess) (reg x))
               (branch (label end-newton))
               (assign guess (op improve) (reg guess) (reg x))
               (goto (label improve))
               end-newton))


#| Exercise 5.4
Specify register machines that implement each of the following procedures.
For each machine, write a controller instruction sequence and draw a
diagram showing the data paths.

Recursive exponentiation:

  (define (expt b n)
    (if (= n 0)
        1
        (* b
           (expt b (- n 1)))))

Iterative exponentiation:

  (define (expt b n)
    (define (expt-iter counter product)
      (if (= counter 0)
          product
          (expt-iter (- counter 1)
                     (* b product))))
    (expt-iter n 1))
|#

(define-register-machine recursive-expt
  #:registers (n b result stored-pc counter)
  #:ops       (* - = +)
  #:assembly  ((assign stored-pc (label immediate))
               (assign counter (const 0))
               start
               (test (op =) (reg n) (reg counter)) ;; if n == 0
               (branch (label immediate))
               (assign stored-pc (label stkretn))
               (save b)
               (assign counter (op +) (reg counter) (reg n))
               (goto (label start))
               ;; now sum our values by popping off `counter' elts from the stack
               stkretn
               (assign result (op *) (reg result) (reg b))
               ;; store our popped value in `result'
               (assign counter (op -) (reg counter) (const 1))
               (test (op =) (const 0) (reg counter))
               (branch (label done))
               (goto (label stkretn))
               ;; We're done, store '2' in 'eax'
               immediate
               (assign result (const 1))
               (goto (reg stored-pc))
               done))

(define-register-machine iter-expt
  #:registers (counter n b result)
  #:ops       (* - = +)
  #:assembly  ((assign result (const 1))
               (assign counter (const 1))
               for-loop
               (assign result (op *) (reg result) (reg b))
               (test (op =) (reg n) (reg counter)) ;; is n == counter
               (branch (label done))
               (assign counter (op +) (reg counter) (const 1))
               (goto (label for-loop))
               done))



(if inside-repl? 'ready ;; we want the repl available ASAP if were inside emacs
    (begin
      ;; load our tests
      (load "test/machine.scm")))
