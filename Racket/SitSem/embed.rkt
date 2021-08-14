#lang s-exp "SitSem.rkt"
(require rackunit/turnstile+
         macrotypes/postfix-in
         (postfix-in - racket/base)
         racket/pretty
         syntax/parse/define  ;define-simple-macro
         (for-syntax syntax/id-table
                     syntax/stx
                     racket/pretty
                     (postfix-in - racket/base)
                     ))

(begin-for-syntax
  (define-syntax-class prelink
    (pattern (obj objemb))))

(define-syntax (embed-sit stx)
  (syntax-parse stx
    [(_ sit)
     #:with prefix (format-id #'sit "~a." (cadr (syntax->datum #'sit)))
     #'(require (prefix-in prefix sit))]))

(define-for-syntax (prettyp prfx v)
  (println (string-append prfx (pretty-format v))))

(define-syntax (link stx)
  (syntax-parse stx
    [(_ sit (prelink:prelink ...))
     #:with prefix (format-id #'sit "~a." (cadr (syntax->datum #'sit)))
     #:do [(define (addprfx s) (format-id #'s "~a~a" #'prefix s))]
     #:with (prfx-obj ...) (stx-map addprfx #'(prelink.objemb ...))
     ;#:with name/id-table (format-id #'sit "~aid-table" #'prefix)
     #:with id-table (stx-map (λ (x y) (cons x y))
                              #'(prelink.obj ...) #'(prfx-obj ...))
     ;#:do [(pretty-print (syntax-debug-info #'name/id-table))]
     #:do [(prettyp "ID-TABLE: " #'id-table)]
     ;(define name/id-table (make-rename-transformer #'id-table))
     #'id-table
     ]))


(module RB "SitSem.rkt"
  (provide man mh mb)
  (define-datatype man : Type
    [mh : man] [mb : man]))

(define-datatype man : Type
  [o : man])

(embed-sit 'RB)
RB.mh
(check-type RB.mh : RB.man)

(begin-for-syntax
  (define-syntax-class link
    (pattern ((obj . objemb) ...))))

(define-syntax (with-link stx)
  (syntax-parse stx
    [(_ sit:id (prelink:prelink ...) body ...)
     #:with prefix (format-id #'sit "~a." (syntax-e #'sit))
     #:do [(define (addprfx s) (format-id #'s "~a~a" #'prefix s))]
     #:with (prfx-obj ...) (stx-map addprfx #'(prelink.objemb ...))
     #:with link (stx-map (λ (x y) (cons x y))
                          #'(prelink.obj ...) #'(prfx-obj ...))
     #:with (((o1 . o2) ...) ...) (variants #'link)
     #'(#%app- values-
               (let- ([o1 o2] ...)
                     body ...) ...)]))

(with-link RB ([o mh] [o mb])
  (#%app- println- RB.mb)
  o)

;; simpler variant
(define-syntax (with-link2 stx)
  (syntax-parse stx
    [(_ (prelink:prelink ...) body ...)
     #:with link (stx-map (λ (x y) (cons x y))
                          #'(prelink.obj ...) #'(prelink.objemb ...))
     #:with (((o1 . o2) ...) ...) (variants #'link)
     #'(#%app- values-
               (let- ([o1 o2] ...)
                     body ...) ...)]))

(with-link2 ([o RB.mh] [o RB.mb])
  (#%app- print- RB.mb)
  o)

; with local-require
(define-syntax (with-link3 stx)
  (syntax-parse stx
    [(_ sit (prelink:prelink ...) body ...)
     #:with link (stx-map (λ (x y) (cons x y))
                          #'(prelink.obj ...) #'(prelink.objemb ...))
     #:with (((o1 . o2) ...) ...) (variants #'link)
     #'(let- ()
             (local-require- sit)
             (#%app- values-
                     (let- ([o1 o2] ...)
                           body ...) ...))]))
(with-link3 'RB ([o mh] [o mb])
  (#%app- print- mh)
  (#%app- print- o)
  (check-type mh : man)
  ;(check-type o : man)  ;not working
  o)
