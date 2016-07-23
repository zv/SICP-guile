
                                        ; Utility fns
(define (eval-+ exp env)
  (fold + 0 (map (λ (e) (zeval e env)) (operands exp))))

(define (eval-- exp env)
  (- (zeval (cadr exp) env)
     (zeval (caddr exp) env)))

(define (eval-= exp env)
  (=
   (zeval (car (operands exp)) env)
   (zeval (cadr (operands exp)) env)))

(install-procedure `(+ ,eval-+))
(install-procedure `(- ,eval--))
(install-procedure `(= ,eval-=))


                                        ; Analysis Utils
(define (analyze-+ exp)
  (λ (env) (eval-+ exp env)))

(define (analyze-- exp)
  (λ (env) (eval-- exp env)))

(define (analyze-= exp)
  (λ (env) (eval-= exp env)))

(install-analyze-procedure `(+ ,analyze-+))
(install-analyze-procedure `(- ,analyze--))
(install-analyze-procedure `(= ,analyze-=))
