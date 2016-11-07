;; -*- mode: scheme; fill-column: 75; comment-column: 50; coding: utf-8; geiser-scheme-implementation: guile -*-
(use-modules (srfi srfi-1)
             (ice-9 popen)
             (ice-9 hash-table)
             (ice-9 unicode)
             (srfi srfi-98)
             (ice-9 rdelim))

;; (srfi srfi-13)) ; for 'string-join'

;; add machine
;; hook machine register
;; process table

(define (template format-string . format-args)
  (apply format `(#f
                  ,format-string
                  ,@format-args)))

(include "/home/zv/z/practice/sicp/machine/register.scm")

;; We use special box-building characters, we need to set the appropriate locale.
(setlocale LC_ALL "")

(define *input-prompt*  ">>> ")
(define *assembly-context* 20)
(define *stack-context* 15)
(define *opcode-padding* 15)
(define *command-table* '(next step continue bp))

(define *machine*
  (make-machine
    '(n temp retval retaddr)
    `((= ,=) (+ ,+) (- ,-) (* ,*))
    '((goto (label machine-start))

        ;;; procedure fact
      fact
      (pop retaddr)       ; return address
      (pop temp)          ; argument
      (push n)                ; push caller's n and retaddr
      (push retaddr)
      (movw n (reg temp))   ; working on n
      (test (op =) (reg n) (const 1))
      (jeq (label fact-base))
      (movw temp (op -) (reg n) (const 1))
                                                  ; prepare for the recursive call:
                                                  ;  push the argument and return value on stack
      (push temp)
      (movw retaddr (label fact-after-rec-return))
      (push retaddr)
      (goto (label fact))     ; the recursive call
      fact-after-rec-return
      (movw retval (op *) (reg retval) (reg n))
      (goto (label fact-end))

      fact-base
      (movw retval (const 1))

      fact-end
                                                  ; pop the caller's registers we've pushd
      (pop retaddr)
      (pop n)
      (goto (reg retaddr))    ; return to caller
        ;;; end procedure fact

      machine-start
                                                  ; to call fact, push n and a return address on stack
                                                  ; and jump to fact
      (push n)
      (movw retaddr (label machine-end))
      (push retaddr)
      (goto (label fact))

      machine-end
      )))

;; initialize machine
(map (λ (elt) (set-register-contents! *machine* (car elt) (cdr elt))) '((n . 10)))

(*machine* 'init)

(define *ansi-color-tables*
  (alist->hash-table '((CLEAR . "0")
                       (RESET . "0")
                       (BOLD . "1")
                       (DARK . "2")
                       (UNDERLINE . "4")
                       (UNDERSCORE . "4")
                       (BLINK . "5")
                       (REVERSE . "6")
                       (CONCEALED . "8")
                       (BLACK . "30")
                       (RED . "31")
                       (GREEN . "32")
                       (YELLOW . "33")
                       (BLUE . "34")
                       (MAGENTA . "35")
                       (CYAN . "36")
                       (WHITE . "37")
                       (ON-BLACK . "40")
                       (ON-RED . "41")
                       (ON-GREEN . "42")
                       (ON-YELLOW . "43")
                       (ON-BLUE . "44")
                       (ON-MAGENTA . "45")
                       (ON-CYAN . "46")
                       (ON-WHITE . "47"))))

(define (color . lst)
  (let ((color-list
         (remove not
                 (map (λ (color) (hash-ref *ansi-color-tables* color)) lst))))
    (if (null? color-list)
        ""
        (string-append
         (string #\esc #\[)
         (string-join color-list ";" 'infix)
         "m"))))

(define (colorize-string str . color-list)
  (string-append
   (apply color color-list)
   str
   (color 'RESET)))

(define (clear) (system "tput clear"))


(define break (integer->char #x2500)) ;; Box-drawing char '─'
(define arrow "🡆")

;; Because the terminal shell operates in it's own process, we need a fluid <-> thread binding
(define (terminal-width)
  (or (let* ((port (open-input-pipe "tput cols"))
             (str  (read-line port))
             (w (false-if-exception (string->number str))))
        (close-pipe port)
        (and (integer? w) (exact? w) (> w 0) w))
      72))

(define (build-header hdr)
  "Print a line of the format ─── HDR ────"
  (let* ([colored-hdr (colorize-string hdr 'YELLOW)]
         [left (format #f "~a ~a " (make-string 7 break) colored-hdr)]
         [len (string-length left)])
    (string-pad-right left (+ 9 (terminal-width)) break)))

(define (print-registers regs)
  (define (print reg)
    (format #t " ~a ~s ~%"
            (string-pad-right (colorize-string (symbol->string (car reg)) 'BOLD) 30)
            (cdr reg)))
  (map print regs))


(define (element-index e lst)
  (cond [(eqv? e (caar lst)) 0]
        [else (+ (element-index e (cdr lst)) 1)]))

(define (extract-readable elt) (if (pair? elt) (caar elt) elt))

(define (extract-registers machine)
  (map
   (λ (register)
     (cons (car register)
           (extract-readable (get-contents (cadr register)))))
   (remove (λ (elt) (eq? (car elt) 'pc)) (machine 'dump-registers))))

(define (wrap-rows str n)
  "Wrap a string to a max of `n' rows"
  (define (next lines ctr)
    (cond
     ((= ctr n) "")
     ((null? lines)
      (string-append "\n" (next lines (+ ctr 1))))
     (else
      (string-append (car lines)
                     "\n"
                     (next (cdr lines) (+ ctr 1))))))
  (next (string-split str #\newline) 0))

(define (format-stack stk instr-seq max)
  (define (next rest ctr)
    (cond
     ((= ctr max) " [+]\n")
     ((null? rest) "")
     (else
      (let ((head (car rest)))
        (string-append
         (format #f " [~a] ~a\n" (colorize-string (number->string ctr)
                                                  (if (= ctr 0) 'BOLD 'DARK))
                 (if (pair? head)
                     (format #f "*0x~4,'0x" (element-index (caar head) instr-seq))
                     head)
                 ;; (extract-readable head)
                 )
         (next (cdr rest) (+ 1 ctr)))))))

  (next stk 0))

;; TODO REWRITE THIS FUCKING JUNK
(define (format-instr insts instr-seq)
  (define (format-instr inst first)
   (define (format-arg arg)
    (match arg
      [('reg var)    (template "~a" var)]
      [('const var)  (template "$~x" var)]
      [('label var)  (template ".~a" var)]
      [('op var)     (template "~a" var)]
      [var           (template "~a" var)]))
   (cond
    [(null? inst) "\n"]
    [else
     (string-append
      (if first
          (string-pad-right (template " 0x~4,'0x\t~a"
                                      (element-index inst instr-seq)
                                      (format-arg (car inst)))
                            *opcode-padding*)
          (format-arg (car inst)))
      " "
      (format-instr (cdr inst) #f)
      )]))

  (define (process instrs first)
    (cond
     [(null? instrs) ""]
     [else
      (string-append
       (if first arrow " ")
       (format-instr (caar instrs) #t)
                     (process (cdr instrs) #f))]))

  (wrap-rows (process insts #t) *assembly-context*)
  )

(define (print-machine-state machine)
  (format #t "~a\n\n" (build-header "Assembly"))

  (display (format-instr (get-contents (get-register machine 'pc))
                         (machine 'dump-instruction-seq)))

  (format #t "\n")
  (format #t "~a\n" (build-header "Registers"))
  (print-registers (extract-registers machine))

  (format #t "~a\n" (build-header "Memory"))
  (format #t "~a\n" (build-header "Stack"))

  (display (format-stack ((machine 'stack) 'raw)
                         (machine 'dump-instruction-seq)
                         *stack-context*))

  (format #t "~a\n" (make-string (terminal-width) break)))
  

(define (driver-loop)
  (clear)
  (print-machine-state *machine*)
  (display *input-prompt*)
  (let ([input (read-line)])
    (match input
      ["q"      (exit)]
      ["quit"   (exit)]
      ["step" ((*machine* 'step))]
      ["j"    ((*machine* 'step))]
      [_      ((*machine* 'step))])
    (driver-loop)))

(driver-loop)
