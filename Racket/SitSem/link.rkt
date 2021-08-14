#lang racket/base
(require racket/list
         syntax/stx)

(provide variants)

(define (snoc v l) (reverse (cons v (reverse l))))

;; tbl = syntax list, result = list of syntaxes
(define (gather tbl)
  (stx-map (λ (lp) (cons (stx-car (stx-car lp))
                         (foldl (λ (v l) (snoc (stx-cdr v) l))
                                '() lp)))
           (group-by (λ (x) (stx-car x)) (stx->list tbl)
                     bound-identifier=?)))

;; cons to every list of lists in l
;; l = list of lists
(define (mult-cons p l)
  (if (null? l)
      (list (list p))
      (map (λ (x) (cons p x))
           l)))

(define (variants tbl)
  (foldr (λ (v l) (append-map (λ (x) (mult-cons (cons (car v) x) l))
                              (cdr v)))
         '() (gather tbl)))
