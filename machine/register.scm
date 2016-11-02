;; -*- mode: scheme; fill-column: 75; comment-column: 50; coding: utf-8; geiser-scheme-implementation: guile -*-

(define (make-machine register-names ops controller-text)
  "`Make-machine' then extends this basic model (by sending it
messages) to include the registers, operations, and controller of the
particular machine being defined.  First it allocates a register in the
new machine for each of the supplied register names and installs the
designated operations in the machine.  Then it uses an 'assembler'
(described below in section *Note 5-2-2::) to transform the controller
list into instructions for the new machine and installs these as the
machine's instruction sequence.  `Make-machine' returns as its value
the modified machine model. "
  (let ((machine (make-new-machine)))
    (for-each (lambda (register-name)
                ((machine 'allocate-register) register-name))
              register-names)
    ((machine 'install-operations) ops)
    ((machine 'install-instruction-sequence)
     (assemble controller-text machine))
    machine))


                                      ; Stack

(define (make-stack)
  "We can also represent a stack as a procedure with local state.  The
procedure `make-stack' creates a stack whose local state consists of a
list of the items on the stack.  A stack accepts requests to `push' an
item onto the stack, to `pop' the top item off the stack and return it,
and to `initialize' the stack to empty."
  (let ((s '()))
    (define (push x)
      (set! s (cons x s)))
    (define (pop)
      (if (null? s)
          (error "Empty stack -- POP")
          (let ((top (car s)))
            (set! s (cdr s))
            top)))
    (define (initialize)
      (set! s '())
      'done)
    (define (dispatch message)
      (cond ((eq? message 'push) push)
            ((eq? message 'pop) (pop))
            ((eq? message 'initialize) (initialize))
            (else (error "Unknown request -- STACK"
                         message))))
    dispatch))

(define (pop stack)
  (stack 'pop))

(define (push stack value)
  ((stack 'push) value))


                                        ; Register
(define (make-register name)
  (let ((contents '*unassigned*))
    (define (dispatch message)
      (cond ((eq? message 'get) contents)
            ((eq? message 'set)
             (lambda (value) (set! contents value)))
            (else
             (error "Unknown request -- REGISTER" message))))
    dispatch))

(define (get-contents register)
  (register 'get))

(define (set-contents! register value)
  ((register 'set) value))



                                        ; The Basic Machine


(define (make-new-machine)
  (let ((pc (make-register 'pc))
        (flag (make-register 'flag))
        (stack (make-stack))
        (the-instruction-sequence '()))
    (let ((the-ops
           (list (list 'initialize-stack
                       (lambda () (stack 'initialize)))))
          (register-table
           (list (list 'pc pc)
                 (list 'flag flag))))

      (define (allocate-register name)
        (if (assoc name register-table)
            (error "Multiply defined register: " name)
            (set! register-table
              (cons (list name (make-register name))
                    register-table)))
        'register-allocated)
      (define (lookup-register name)
        (let ((val (assoc name register-table)))
          (if val (cadr val)
              (error "Unknown register:" name))))
      (define (execute)
        (let ((insts (get-contents pc)))
          (if (null? insts) 'done
              (begin
                ((instruction-execution-proc (car insts)))
                (execute)))))
      (define (dispatch message)
        (match message
          ['start
           (set-contents! pc the-instruction-sequence)
           (execute)]
          ['install-instruction-sequence
           (λ (seq) (set! the-instruction-sequence seq))]
          ['allocate-register allocate-register]
          ['get-register lookup-register]
          ['install-operations
           (λ (ops) (set! the-ops (append the-ops ops)))]
          ['stack stack]
          ['operations the-ops]
          [_
           (error "Unknown request -- MACHINE" message)]))
      dispatch)))
