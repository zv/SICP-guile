#lang sicp
(#%require sicp-pict)
;; -----------------------------------------------------------
;; Utilities
;; -----------------------------------------------------------
(define (flipped-pairs painter)
  (let [(painter2 (beside painter (flip-vert painter)))]
    (below painter2 painter2)))
(define (right-split painter n)
  (if (= n 0) painter
      (let [(smaller (right-split painter (- n 1)))]
        (beside painter (below smaller smaller)))))
(define (corner-split painter n)
  (if (= n 0) painter
      (let [(up (up-split painter (- n 1)))
            (right (right-split painter (- n 1)))]
        (let [(top-left (beside up up))
              (bottom-right (below right right))
              (corner (corner-split painter (- n 1)))]
          (beside (below painter top-left)
                  (below bottom-right corner))))))

(define (square-of-four tl tr bl br)
  (lambda (painter)
    (let ((top (beside (tl painter)
                       (tr painter)))
          (bottom (beside (bl painter)
                          (br painter))))
      (below bottom top))))
(define (flipped-pairs-z painter)
  (let ((combine4
         (square-of-four identity
                         flip-vert
                         identity
                         flip-vert)))
    (combine4 painter)))
;; -----------------------------------------------------------
;;; /Utilities (End)
;; -----------------------------------------------------------

;; 2.44
(define (up-split painter n)
  (if (= n 0)
      painter
      (let [(smaller (up-split painter (- n 1)))]
        (below painter
               (beside smaller smaller)))))

;; 2.45
(define (split stepa stepb)
  (define (new-painter painter n)
    (if (= n 0) painter
        (let [(smaller (new-painter painter (dec n)))]
          (stepa painter (stepb smaller smaller)))))
  painter)

(define right-split-z (split beside below))
(define up-split-z (split below beside))

;; 2.46
