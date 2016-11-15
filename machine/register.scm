;; -*- mode: scheme; fill-column: 75; comment-column: 50; coding: utf-8; geiser-scheme-implementation: guile -*-
(use-modules (ice-9 q))
(use-modules (srfi srfi-111))
(use-modules (srfi srfi-26))

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
          (error "Empty stack: POP")
          (let ((top (car s)))
            (set! s (cdr s))
            top)))
    (define (initialize)
      (set! s '())
      'done)
    (define (dispatch msg)
      (match msg
        ['push push]
        ['pop (pop)]
        ['initialize (initialize)]
        ['raw s]
        [_ (error "Unknown request -- STACK" msg)]))
    dispatch))

(define (pop stack) (stack 'pop))
(define (push stack value) ((stack 'push) value))

                                                  ; Register
(define (make-register name)
  (let ([contents (box #nil)]
        [before-set-hook (make-hook 3)])
    (define (dispatch message)
      (match message
        ['get (unbox contents)]
        ['set (λ (value)
           (run-hook before-set-hook name (unbox contents) value)
           (set-box! contents value))]
        ['add-hook (λ (fn) (add-hook! before-set-hook fn))]
        ['remove-hook! (λ (fn) (remove-hook! before-set-hook fn))]
        [_ (error "Unknown request -- REGISTER" message)]))
    dispatch))

(define (get-contents register) (register 'get))
(define (set-contents! register value) ((register 'set) value))
(define (get-register machine reg-name) ((machine 'get-register) reg-name))
(define (set-register-hook register fn) ((register 'add-hook) fn))
(define (remove-register-hook register fn) ((register 'remove-hook) fn))


                                                  ; The Basic Machine

(define (make-new-machine)
  "The `make-new-machine' procedure, shown in*Note , constructs an object
whose local state consists of a stack, an initially empty instruction
sequence, a list of operations that initially contains an operation to
initialize the stack, and a 'register table' that initially contains two
registers, named `flag' and `pc'"
  (let* ([pc     (make-register 'pc)]
         [flag   (make-register 'flag)]
         [stack  (make-stack)]
         [the-instruction-sequence '()]
         [the-ops `((initialize-stack ,(λ () (stack 'initialize))))]
         [register-table `((pc ,pc)
                           (flag ,flag))])
    (define (allocate-register name)
      (if (assoc name register-table)
          (error "Multiply defined register: " name)
          (set! register-table
            (cons (list name (make-register name))
                  register-table)))
      'register-allocated)
    (define (lookup-register name)
      (let ((val (assoc name register-table)))
        (if val
            (cadr val)
            (error "Unknown register:" name))))
    (define (execute)
      (match (get-contents pc)
        [() 'done]
        [insts (begin
                 ((instruction-execution-proc (car insts)))
                 (execute))]))
    (define (step)
      (let ((insts (get-contents pc)))
        (if (null? insts) 'done
            (begin
              ((instruction-execution-proc (car insts)))))))
    (define (hook-registers fn)
      (map (λ (elt) (set-register-hook (cadr elt) fn)) register-table))
    (define (dispatch message)
      (match message
        ['init
         (set-contents! pc the-instruction-sequence)]
        ['start
         (set-contents! pc the-instruction-sequence)
         (execute)]
        ['dump-instruction-seq the-instruction-sequence]
        ['step step]
        ['install-instruction-sequence
         (λ (seq) (set! the-instruction-sequence seq))]
        ['allocate-register allocate-register]
        ['get-register lookup-register]
        ['install-operations
         (λ (ops) (set! the-ops (append the-ops ops)))]
        ['stack stack]
        ['install-register-hook (cut hook-registers <>)]
        ['operations the-ops]
        ['dump-registers  register-table]
        [_ (error "Unknown request -- MACHINE" message)]))
    dispatch))

(define (start machine)
  (machine 'start))

(define (get-register-contents machine register-name)
  (get-contents (get-register machine register-name)))

(define (set-register-contents! machine register-name value)
  (set-contents! (get-register machine register-name) value)
  'done)

(define (get-register machine reg-name)
  ((machine 'get-register) reg-name))


                                                  ; Assembler

(define (assemble controller-text machine)
  "The `assemble' procedure is the main entry to the assembler.  It
takes the controller text and the machine model as arguments and
returns the instruction sequence to be stored in the model.  `Assemble'
calls `extract-labels' to build the initial instruction list and label
table from the supplied controller text.  The second argument to
`extract-labels' is a procedure to be called to process these results:
This procedure uses `update-insts!' to generate the instruction
execution procedures and insert them into the instruction list, and
returns the modified list."
  (extract-labels controller-text
                  (lambda (insts labels)
                    (update-insts! insts labels machine)
                    insts)))

(define (extract-labels text receive)
  "`Extract-labels' takes as arguments a list `text' (the sequence of
controller instruction expressions) and a `receive' procedure. `Receive'
will be called with two values: (1) a list `insts' of instruction data
structures, each containing an instruction from `text'; and (2) a table
called `labels', which associates each label from `text' with the position
in the list `insts' that the label designates.

`Extract-labels' works by sequentially scanning the elements of the
`text' and accumulating the `insts' and the `labels'. If an element is a
symbol (and thus a label) an appropriate entry is added to the `labels'
table. Otherwise the element is accumulated onto the `insts' list."
  (if (null? text) (receive '() '())
      (extract-labels (cdr text)
                      (lambda (insts labels)
                        (let ((next-inst (car text)))
                          (if (symbol? next-inst)
                              (receive insts
                                  (cons (make-label-entry next-inst insts)
                                        labels))

                              (receive
                                  (cons (make-instruction next-inst) insts)
                                  labels)))))))


(define (update-insts! insts labels machine)
  "`Update-insts!' modifies the instruction list, which initially contains
only the text of the instructions, to include the corresponding execution
procedures: "
  (let ((pc (get-register machine 'pc))
        (flag (get-register machine 'flag))
        (stack (machine 'stack))
        (ops (machine 'operations)))
    (for-each
     (lambda (inst)
       (set-instruction-execution-proc!
        inst
        (make-execution-procedure (instruction-text inst)
                                  labels
                                  machine
                                  pc
                                  flag
                                  stack
                                  ops)))
     insts)))

(define (make-instruction text) (list text
                                      '()
                                      '()))
(define (instruction-text inst) (car inst))
(define (instruction-execution-proc inst) (cadr inst))
(define (set-instruction-execution-proc! inst proc) (set-car! (cdr inst) proc))


;; Elements of the label table are pairs:

(define (make-label-entry label-name insts)
  (cons label-name insts))

;; Entries will be looked up in the table with

(define (lookup-label labels label-name)
  (let ((val (assoc label-name labels)))
    (if val
        (cdr val)
        (error "Undefined label -- ASSEMBLE" label-name))))


                                                  ; Generating Execution Procedures
(define (make-execution-procedure inst labels machine pc flag stack ops)
  (match (car inst)
    ['movw     (make-assign inst machine labels ops pc)]
    ['test     (make-test inst machine labels ops flag pc)]
    ['jeq      (make-branch inst machine labels flag pc)]
    ['goto     (make-goto inst machine labels pc)]
    ['push     (make-save inst machine stack pc)]
    ['pop      (make-restore inst machine stack pc)]
    ['perform  (make-perform inst machine labels ops pc)]
    [_ (error "Unknown instruction type -- ASSEMBLE" inst)]))

(define (make-assign inst machine labels operations pc)
  "`Make-assign' extracts the target register name (the second element of
the instruction) and the value expression (the rest of the list that forms
the instruction) from the `assign' instruction using the selectors "
  (let ((target
         (get-register machine (assign-reg-name inst)))
        (value-exp (assign-value-exp inst)))
    (let ((value-proc
           (if (operation-exp? value-exp)
               (make-operation-exp
                value-exp machine labels operations)
               (make-primitive-exp
                (car value-exp) machine labels))))
      (lambda ()                ; execution procedure for assign
        (set-contents! target (value-proc))
        (advance-pc pc)))))

(define (assign-reg-name assign-instruction) (cadr assign-instruction))
(define (assign-value-exp assign-instruction) (cddr assign-instruction))

;; Move the instruction pointer one forward
(define (advance-pc pc) (set-contents! pc (cdr (get-contents pc))))



(define (make-test inst machine labels operations flag pc)
  "`Make-test' handles `test' instructions in a similar way. It extracts
the expression that specifies the condition to be tested and generates an
execution procedure for it. At simulation time, the procedure for the
condition is called, the result is assigned to the `flag' register, and the
`pc' is advanced:"
  (let ((condition (test-condition inst)))
    (if (operation-exp? condition)
        (let ((condition-proc
               (make-operation-exp
                condition machine labels operations)))
          (lambda ()
            (set-contents! flag (condition-proc))
            (advance-pc pc)))
        (error "Bad TEST instruction -- ASSEMBLE" inst))))

(define (test-condition test-instruction) (cdr test-instruction))


(define (make-branch inst machine labels flag pc)
  " The execution procedure for a `branch' instruction checks the contents
of the `flag' register and either sets the contents of the `pc' to the
branch destination (if the branch is taken) or else just advances the `pc'
(if the branch is not taken). Notice that the indicated destination in a
`branch' instruction must be a label, and the `make-branch' procedure
enforces this. Notice also that the label is looked up at assembly time,
not each time the `branch' instruction is simulated. "
  (let ((dest (branch-dest inst)))
    (if (label-exp? dest)
        (let ((insts
               (lookup-label labels (label-exp-label dest))))
          (lambda ()
            (if (get-contents flag)
                (set-contents! pc insts)
                (advance-pc pc))))
        (error "Bad BRANCH instruction -- ASSEMBLE" inst))))

(define (branch-dest branch-instruction) (cadr branch-instruction))


(define (make-goto inst machine labels pc)
  " A `goto' instruction is similar to a branch, except that the
destination may be specified either as a label or as a register, and there
is no condition to check--the `pc' is always set to the new destination. "
  (let ((dest (goto-dest inst)))
    (cond ((label-exp? dest)
           (let ((insts (lookup-label labels (label-exp-label dest))))
             (lambda () (set-contents! pc insts))))
          ((register-exp? dest)
           (let ((reg (get-register machine (register-exp-reg dest))))
             (lambda ()
               (set-contents! pc (get-contents reg)))))
          (else (error "Bad GOTO instruction -- ASSEMBLE" inst)))))

(define (goto-dest goto-instruction) (cadr goto-instruction))


                                                  ; Other Instructions
;;  The stack instructions `save' and `restore' simply use the stack with
;;  the designated register and advance the `pc':
(define (make-save inst machine stack pc)
  (let ((reg (get-register machine
                           (stack-inst-reg-name inst))))
    (lambda ()
      (push stack (get-contents reg))
      (advance-pc pc))))

(define (make-restore inst machine stack pc)
  (let ((reg (get-register machine
                           (stack-inst-reg-name inst))))
    (lambda ()
      (set-contents! reg (pop stack))
      (advance-pc pc))))

(define (stack-inst-reg-name stack-instruction)
  (cadr stack-instruction))

(define (make-perform inst machine labels operations pc)
  " `make-perform', generates an execution procedure for the action to be
performed. At simulation time, the action procedure is executed and the
`pc' advanced. "
  (let ((action (perform-action inst)))
    (if (operation-exp? action)
        (let ((action-proc
               (make-operation-exp
                action machine labels operations)))
          (lambda ()
            (action-proc)
            (advance-pc pc)))
        (error "Bad PERFORM instruction -- ASSEMBLE" inst))))

(define (perform-action inst) (cdr inst))

                                                  ; Execution procedure for subexpressions

;; The value of a `reg', `label', or `const' expression may be needed for
;; assignment to a register (`make-assign') or for input to an operation
;; (`make-operation-exp', below).  The following procedure generates
;; execution procedures to produce values for these expressions during the
;; simulation:

(define (make-primitive-exp exp machine labels)
  (cond ((constant-exp? exp)
         (let ((c (constant-exp-value exp)))
           (lambda () c)))
        ((label-exp? exp)
         (let ((insts
                (lookup-label labels
                              (label-exp-label exp))))
           (lambda () insts)))
        ((register-exp? exp)
         (let ((r (get-register machine
                                (register-exp-reg exp))))
           (lambda () (get-contents r))))
        (else
         (error "Unknown expression type -- ASSEMBLE" exp))))

(define (register-exp? exp) (tagged-list? exp 'reg))
(define (register-exp-reg exp) (cadr exp))
(define (constant-exp? exp) (tagged-list? exp 'const))
(define (constant-exp-value exp) (cadr exp))
(define (label-exp? exp) (tagged-list? exp 'label))
(define (label-exp-label exp) (cadr exp))

(define (make-operation-exp exp machine labels operations)
  (let ((op (lookup-prim (operation-exp-op exp) operations))
        (aprocs
         (map (lambda (e)
                (make-primitive-exp e machine labels))
              (operation-exp-operands exp))))
    (lambda ()
      (apply op (map (lambda (p) (p)) aprocs)))))

(define (operation-exp? exp)
  (and (pair? exp) (tagged-list? (car exp) 'op)))
(define (operation-exp-op operation-exp)
  (cadr (car operation-exp)))
(define (operation-exp-operands operation-exp)
  (cdr operation-exp))

(define (lookup-prim symbol operations)
  (let ((val (assoc symbol operations)))
    (if val
        (cadr val)
        (error "Unknown operation -- ASSEMBLE" symbol))))


;; from 4.1
(define (tagged-list? exp tag)
  (if (pair? exp)
      (eq? (car exp) tag)
      #f))
