;; -*- mode: scheme; fill-column: 75; comment-column: 50; coding: utf-8; geiser-scheme-implementation: guile -*-

(use-modules (ice-9 popen))
(use-modules (ice-9 unicode))
(use-modules (srfi srfi-98))
(use-modules (ice-9 rdelim))
(use-modules (srfi srfi-1))

;; (srfi srfi-13)) ; for 'string-join'

;; add machine
;; hook machine register
;; process table

(include "/home/zv/z/practice/sicp/machine/register.scm")

;; We use special box-building characters, we need to set the appropriate locale.
(setlocale LC_ALL "")

(define *input-prompt*  ">>> ")
(define *command-table* '(next step continue bp))

(define *machine*
  (make-machine
   '(n b result retn-addr counter) ;; register-names
   `((* ,*) (- ,-) (+ ,+) (= ,=));; proc-ops
   ;; assembly
   '((assign retn-addr (label immediate))
    (assign counter (const 0))
    start
    (test (op =) (reg n) (reg counter)) ;; if n == 0
    (branch (label immediate))
    (assign retn-addr (label stkretn))
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
    (goto (reg retn-addr))
    done)))

;; initialize machine
(map (λ (elt) (set-register-contents! *machine* (car elt) (cdr elt))) '((n . 400) (b . 200)))
(*machine* 'init)

(define ansi-color-tables
  (let ((table (make-hash-table 23)))
    (hashq-set! table 'CLEAR "0")
    (hashq-set! table 'RESET "0")
    (hashq-set! table 'BOLD  "1")
    (hashq-set! table 'DARK  "2")
    (hashq-set! table 'UNDERLINE "4")
    (hashq-set! table 'UNDERSCORE "4")
    (hashq-set! table 'BLINK "5")
    (hashq-set! table 'REVERSE "6")
    (hashq-set! table 'CONCEALED "8")
    (hashq-set! table 'BLACK "30")
    (hashq-set! table 'RED "31")
    (hashq-set! table 'GREEN "32")
    (hashq-set! table 'YELLOW "33")
    (hashq-set! table 'BLUE "34")
    (hashq-set! table 'MAGENTA "35")
    (hashq-set! table 'CYAN "36")
    (hashq-set! table 'WHITE "37")
    (hashq-set! table 'ON-BLACK "40")
    (hashq-set! table 'ON-RED "41")
    (hashq-set! table 'ON-GREEN "42")
    (hashq-set! table 'ON-YELLOW "43")
    (hashq-set! table 'ON-BLUE "44")
    (hashq-set! table 'ON-MAGENTA "45")
    (hashq-set! table 'ON-CYAN "46")
    (hashq-set! table 'ON-WHITE "47")
    table))

(define (color . lst)
  (let ((color-list
         (remove not
                 (map (lambda (color) (hashq-ref ansi-color-tables color)) lst))))
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
(define asm
"0x0001	iter-fact+1	mov result 1
0x0002	iter-fact+2	mov counter 1
0x0003	iter-fact+3	mov result (* result b)
0x0004	iter-fact+4	test (= n counter)
0x0005	iter-fact+5	branch .done
0x0006	iter-fact+6	assign counter (+ counter 1)
0x0007	iter-fact+7	goto .for-loop
")

(define test-regs
  "pc		0x0
flag		#t
result		1267650600228229401496703205376
b		2
n		100
counter		100
")

(define test-registers
  '((result . 1267650600228229401496703205376)
    (b . 2)
    (n . 100)
    (counter . 100)
    (flag . #t)))

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

(define* (print-registers frame #:optional (port (current-output-port)) #:key (per-line-prefix "  "))
  (define (print fmt val)
    (display per-line-prefix port)
    (run-hook before-print-hook val)
    (format port fmt val))

  (format port "~aRegisters:~%" per-line-prefix)
  (let ((ip (machine-instruction-pointer machine)))
    (format "pc = #x~x" ip)
    (let ((info (find-program-debug-info ip)))
      (when info
        (let ((addr (program-debug-info-addr info)))
          (format port " (#x~x + ~d * 4)" addr (/ (- ip addr) 4)))))
    (newline port))
  (print "sp = ~a\n" (frame-stack-pointer frame))
  (print "fp = ~a\n" (frame-address frame)))

(define (print-registers regs)
  (define (print reg)
    (format #t " ~a ~s ~%"
            (string-pad-right (colorize-string (symbol->string (car reg)) 'BOLD) 30)
            (cdr reg)))
  (map print regs))


(define (extract-registers machine)
  (map
   (λ (rega)
     (cons (car rega)
           (get-contents (cadr rega))))
   (remove
    (λ (elt)
      (eq? (car elt) 'pc))
    (*machine* 'dump-registers)))
  ;; (map
  ;;  (λ (reg) (cons (car reg)
  ;;                 (get-contents (get-register machine (car reg)))))
  ;;  (machine 'dump-registers))
  )

(define (print-machine-state machine)
  (format #t "~a\n" (build-header "Assembly"))
  (format #t "~y" (map car (get-contents (get-register machine 'pc))))
  (format #t "~a\n" (build-header "Registers"))
  (print-registers (extract-registers machine)))

(define (print-stuff)
  (format #t "~a\n" (build-header "Assembly"))
  (display asm)
  (format #t "~a\n" (build-header "Registers"))
  (print-registers test-registers)
  (format #t "~a\n" (build-header "Stack"))
  (display asm)
  (format #t "~a\n" (make-string (terminal-width) break)))

  


(define (base-driver-loop)
  (clear)
  (print-machine-state *machine*)
  ((*machine* 'step))
  (display *input-prompt*)
  (let* ([input (read-char)]
         [output ">>"])
    1)
  (base-driver-loop))

(base-driver-loop)
