(use-modules (oop goops))
(use-modules (ice-9 format))
(use-modules (ice-9 match))
(use-modules (ice-9 pretty-print))
(use-modules (ice-9 q))


                                        ; Stack
(define (pop stk) (q-pop! stk))
(define (push stk value) (q-push! stk value))


                                        ; Register
(define-class <register> ()
  (contents #:init-value '*unassigned*
            #:getter get-contents
            #:setter set-contents!))




(define-class <register-machine> ()
  (registers #:init-thunk (make-hash-table 31))
  (pc #:init-value #nil
      #:allocation #:virtual
      #:slot-ref (λ (o) (fetchr o 'pc))
      #:slot-set (λ (o a) (setr o 'pc)))
  (flag #:init-value #nil
        #:allocation #:virtual
        #:slot-ref (λ (o) (fetchr o 'flag))
        #:slot-set (λ (o a) (setr o 'flag))))

