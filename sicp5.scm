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

(define* (build-rmachine #:key registers ops assembly)
  (let* ([register-names
          (map (λ (elt) (if (list? elt) (car elt) elt)) registers)]
         [mach (make-machine register-names ops assembly)])
    (map (λ (elt)
           (if (list? elt)
               (set-register-contents! mach (car elt) (cadr elt))))
         registers)
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
  #:ops       ((> ,>) (* ,*) (+ ,+))
  #:assembly  (init
               (assign counter (const 1))
               (assign product (const 1))
               loop
               (test (op >) (reg counter) (reg n))
               (branch (label end-fib))
               (assign product (op *) (reg counter) (reg product))
               (assign counter (op +) (reg counter) (const 1))
               (goto (label loop))
               end-fib))

(machine-run factorial '((n . 6)))

(if inside-repl? 'ready ;; we want the repl available ASAP if were inside emacs
    (begin
      ;; load our tests
      (load "test/machine.scm")))
