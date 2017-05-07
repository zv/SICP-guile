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

(define (reg-debug format-string . format-args)
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
    ((define-register-machine var #:assembly assembly)
     (define var (make-machine 'assembly)))))


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
  #:assembly  ((movw counter (const 1))
               (movw product (const 1))
               loop
               (test (op >) (reg counter) (reg n))
               (jeq (label end-fib))
               (movw product (op *) (reg counter) (reg product))
               (movw counter (op +) (reg counter) (const 1))
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
  #:assembly  ((movw guess (const 1.0))
               improve
               (test (op newton/good-enough?) (reg guess) (reg x))
               (jeq (label end-newton))
               (movw guess (op newton/improve) (reg guess) (reg x))
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
  #:assembly  ((movw retnaddr (label immediate))
               (movw counter (const 0))
               start
               (test (op =) (reg n) (reg counter)) ;; if n == 0
               (jeq (label immediate))
               (movw retnaddr (label stkretn))
               (push b)
               (movw counter (op +) (reg counter) (reg n))
               (goto (label start))
               ;; now sum our values by popping off `counter' elts from the stack
               stkretn
               (movw result (op *) (reg result) (reg b))
               ;; store our popped value in `result'
               (movw counter (op -) (reg counter) (const 1))
               (test (op =) (const 0) (reg counter))
               (jeq (label done))
               (goto (label stkretn))
               ;; We're done, store '2' in 'eax'
               immediate
               (movw result (const 1))
               (goto (reg retnaddr))
               done))

(define-register-machine iter-expt
  #:assembly  ((movw result (const 1))
               (movw counter (const 1))
               for-loop
               (movw result (op *) (reg result) (reg b))
               (test (op =) (reg n) (reg counter)) ;; is n == counter
               (jeq (label done))
               (movw counter (op +) (reg counter) (const 1))
               (goto (label for-loop))
               done))


#| Exercise 5.5 DONE
Hand-simulate the factorial and Fibonacci machines, using some nontrivial
input (requiring execution of at least one recursive call). Show the
contents of the stack at each significant point in the execution. |#


#| Exercise 5.6
Ben Bitdiddle observes that the Fibonacci machine’s controller sequence has
an extra save and an extra restore, which can be removed to make a faster
machine. Where are these instructions? |#

#| Answer:
Both the save & restore of `continue' are useless.
|#

                                                  ; The Simulator


#| Exercise 5.7: Use the simulator to test the machines you designed in Exercise 5.4. |#

 
#| Exercise 5.8
The following register-machine code is ambiguous, because the label `here'
is defined more than once:

  start
    (goto (label here))
  here
    (movw a (const 3))
    (goto (label there))
  here
    (movw a (const 4))
    (goto (label there))
  there

With the simulator as written, what will the contents of register `a' be
when control reaches `there'? Modify the `extract-labels' procedure so that
the assembler will signal an error if the same label name is used to
indicate two different locations. |#

#| Answer: extract-label updated in 57a079eda7d4a0dc58ba2f8324f4b03c55ad27cc |#


#| Exercise 5.9
The treatment of machine operations above permits them to operate on labels
as well as on constants and the contents of registers. Modify the
expression-processing procedures to enforce the condition that operations
can be used only with registers and constants. |#
(define (make-operation-exp exp machine labels operations)
  (let ((op (lookup-prim (operation-exp-op exp) operations))
        (aprocs
         (map (lambda (e)
                (if (or (register-exp? e) (constant-exp? e))
                    (make-primitive-exp e machine labels)
                    (error "neither register nor constant exp in `make-operation-exp'")))
              (operation-exp-operands exp))))
    (lambda ()
      (apply op (map (lambda (p) (p)) aprocs)))))


#| Exercise 5.10
Design a new syntax for register-machine instructions and modify the
simulator to use your new syntax. Can you implement your new syntax without
changing any part of the simulator except the syntax procedures in this
section? |#

#| Answer:
Yes, I can. |#


#| TODO Exercise 5.11
When we introduced `save' and `restore' in section *Note 5-1-4, we didn't
specify what would happen if you tried to restore a register that was not
the last one saved, as in the sequence

    (save y)
    (save x)
    (restore y)

There are several reasonable possibilities for the meaning of
`restore':

  a. `(restore y)' puts into `y' the last value saved on the stack,
     regardless of what register that value came from.  This is
     the way our simulator behaves.  Show how to take advantage of
     this behavior to eliminate one instruction from the Fibonacci
     machine of section *Note 5-1-4:: (*Note Figure 5-12::).

  b. `(restore y)' puts into `y' the last value saved on the
     stack, but only if that value was saved from `y'; otherwise,
     it signals an error.  Modify the simulator to behave this
     way.  You will have to change `save' to put the register name
     on the stack along with the value.

  c. `(restore y)' puts into `y' the last value saved from `y'
     regardless of what other registers were saved after `y' and
     not restored.  Modify the simulator to behave this way.  You
     will have to associate a separate stack with each register.
     You should make the `initialize-stack' operation initialize
     all the register stacks.
|#


#| Exercise 5.12
The simulator can be used to help determine the data paths required for
implementing a machine with a given controller. Extend the assembler to
store the following information in the machine model:

* DONE a list of all instructions, with duplicates removed, sorted by
instruction type (`assign', `goto', and so on);

* DONE a list (without duplicates) of the registers used to hold entry points
(these are the registers referenced by `goto' instructions);

* DONE a list (without duplicates) of the registers that are `save'd or
`restore'd;

* DONE for each register, a list (without duplicates) of the sources from which
it is assigned (for example, the sources for register `val' in the
factorial machine of *Note Figure 5-11 are `(const 1)' and `((op *) (reg n)
(reg val))').

Extend the message-passing interface to the machine to provide access to
this new information. To test your analyzer, define the Fibonacci machine
from Figure 5.12 and examine the lists you constructed.
|#
(define (filter-opcodes text fn)
  "Filter controller text down to those opcodes for which `fn' == #t"
  (map car (filter fn
                   (select-labels text (λ (insts labels) insts)))))

(define (extract-goto-destinations text)
  (fold
   (λ (elt acc)
     (if (member (car elt) acc) acc (append acc elt)))
   '() ;; initial argument to fold
   (map cdadr (filter-opcodes text
                               (λ (inst) (eq? (caar inst) 'goto))))))

(define (extract-stack-manipulations text)
  (fold
   (λ (elt acc)
     (if (member (car elt) acc) acc (append acc elt)))
   '() ;; initial argument to fold
   (map cdr
        (filter-opcodes text
                        (λ (inst)
                          (let ((opcode (caar inst)))
                            (or (eq? opcode 'pop)
                                (eq? opcode 'push))))))))


#| Exercise 5.13
Modify the simulator so that it uses the controller sequence to determine
what registers the machine has rather than requiring a list of registers as
an argument to `make-machine'. Instead of pre-allocating the registers in
`make-machine', you can allocate them one at a time when they are first
seen during assembly of the instructions. |#

#| Answer:
I modified `make-machine' directly to support this change in rev:f68d783
|#


#| Exercise 5.14
Measure the number of pushes and the maximum stack depth required to
compute n! for various small values of n using the factorial machine shown
Figure 5-11. From your data determine formulas in terms of n for
the total number of push operations and the maximum stack depth used in
computing n! for any n > 1. Note that each of these is a linear function of
n and is thus determined by two constants. In order to get the statistics
printed, you will have to augment the factorial machine with instructions
to initialize the stack and print the statistics. You may want to also
modify the machine so that it repeatedly reads a value for n, computes the
factorial, and prints the result (as we did for the GCD machine in Figure
5.4, so that you will not have to repeatedly invoke `get-register-contents',
`set-register-contents!', and `start'. |#


#| Answer:
Because no operations pop elements off the stack until the function
terminates, the total amount of stack space used is 2N - 2 where N is the
space used by a particular stack frame.
|#


#| Exercise 5.15
Add counting "instruction counting" to the register machine simulation.
That is, have the machine model keep track of the number of instructions
executed. Extend the machine model's interface to accept a new message that
prints the value of the instruction count and resets the count to zero. |#

#| Answer:
I've modified `make-new-machine' to return 'instruction-count', and
machine/gui to automatically return this upon every step / continue
|#


#| Exercise 5.16
Augment the simulator to provide for "instruction tracing". That is, before
each instruction is executed, the simulator should print the text of the
instruction. Make the machine model accept `trace-on' and `trace-off'
messages to turn tracing on and off. |#

#| Answer: Added to machine/gui #|


#| Exercise 5.17
Extend the instruction tracing of *Note Exercise 5-16 so that before
printing an instruction, the simulator prints any labels that immediately
precede that instruction in the controller sequence. Be careful to do this
in a way that does not interfere with instruction counting (*Note Exercise
5-15). You will have to make the simulator retain the necessary label
information. |#

#| Answer:
This is already a feature :)
|#


#| TODO Exercise 5.18
Modify the `make-register' procedure of section *Note 5-2-1 so that
registers can be traced. Registers should accept messages that turn tracing
on and off. When a register is traced, assigning a value to the register
should print the name of the register, the old contents of the register,
and the new contents being assigned. Extend the interface to the machine
model to permit you to turn tracing on and off for designated machine
registers. |#


#| TODO Exercise 5.19
Alyssa P. Hacker wants a "breakpoint" feature in the simulator to help her
debug her machine designs. You have been hired to install this feature for
her. She wants to be able to specify a place in the controller sequence
where the simulator will stop and allow her to examine the state of the
machine. You are to implement a procedure

     (set-breakpoint <MACHINE> <LABEL> <N>)

that sets a breakpoint just before the nth instruction after the given
label. For example,

     (set-breakpoint gcd-machine 'test-b 4)

installs a breakpoint in `gcd-machine' just before the assignment to
register `a'. When the simulator reaches the breakpoint it should print the
label and the offset of the breakpoint and stop executing instructions.
Alyssa can then use `get-register-contents' and `set-register-contents!' to
manipulate the state of the simulated machine. She should then be able to
continue execution by saying

     (proceed-machine <MACHINE>)

She should also be able to remove a specific breakpoint by means of

     (cancel-breakpoint <MACHINE> <LABEL> <N>)

or to remove all breakpoints by means of

     (cancel-all-breakpoints <MACHINE>)

|#


#| Exercise 5.20
Draw the box-and-pointer representation and the memory-vector
representation (shown in Figure 5-14) of the list structure produced by

  (define x (cons 1 2))
  (define y (list x x))

with the `free' pointer initially `p1'. What is the final value of `free' ?
What pointers represent the values of `x' and `y' ? |#


#| Answer:

* Cons-cells:

     +---+---+       +---+----+
     | | |  -|------>| | ||||||
     +---+---+       +---+----+
       |               |
       +---------------+
       |
       v
     +---+---+
     | 1 | 2 |
     +---+---+

* car/cdr Adjascency lst

    +---+----+----+----+---+---+
    | 0 | 1  | 2  |  3 | 4 | 5 |
    +---+----+----+----+---+---+
    |   | n1 | p1 | p1 |   |   |
    |   | n2 | p3 | e0 |   |   |
    +---+----+----+----+---+---+
|#


#| TODO Exercise 5.21
Implement register machines for the following procedures. Assume that the
list-structure memory operations are available as machine primitives.

a. Recursive `count-leaves':

        (define (count-leaves tree)
          (cond ((null? tree) 0)
                ((not (pair? tree)) 1)
                (else (+ (count-leaves (car tree))
                         (count-leaves (cdr tree))))))

b. Recursive `count-leaves' with explicit counter:

        (define (count-leaves tree)
          (define (count-iter tree n)
            (cond ((null? tree) n)
                  ((not (pair? tree)) (+ n 1))
                  (else (count-iter (cdr tree)
                                    (count-iter (car tree) n)))))
          (count-iter tree 0))
|#


#| TODO Exercise 5.22
Exercise 3.12 of section 3.3.1 presented an `append' procedure that appends
two lists to form a new list and an `append!' procedure that splices two
lists together. Design a register machine to implement each of these
procedures. Assume that the list-structure memory operations are available
as primitive operations. |#


(if inside-repl? 'ready ;; we want the repl available ASAP if were inside emacs
    (begin
      ;; load our tests
      (load "test/machine.scm")))

