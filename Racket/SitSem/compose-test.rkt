#lang s-exp "SitSem.rkt"
(require rackunit/turnstile+
         macrotypes/postfix-in
         (postfix-in - racket/base)
         racket/pretty
         syntax/parse/define  ;define-simple-macro
         "compose.rkt"
         (only-in macrotypes/typecheck-core typeof)
         (for-syntax syntax/id-table
                     syntax/stx
                     racket/pretty
                     (postfix-in - racket/base)))

(module common "SitSem.rkt"
  (provide ⊥ ⊤ ¬)
  (define-datatype ⊥ : Type)
  (define-datatype ⊤ : Type
    [tt : ⊤])

  (define-typed-syntax (¬ τ) ≫
    [⊢ τ ≫ τ- ⇒ (~Type _)]
    --------
    [≻ (-> τ ⊥)])
  )

(require 'common)

(module RB "SitSem.rkt"
  (require (submod ".." common)
           cur/stdlib/sugar
           (only-in turnstile
                    define-typed-variable)
           rackunit/turnstile)
  (provide man mh mb spy sh sb)
  (define-datatype man : Type
    [mh : man] [mb : man])

  (define-datatype spy : (-> man Type)
    [sh : (spy mh)])
  (check-type (spy mh) : Type)
  (check-type sh : (spy mh))
  (check-type (spy mh) : Type)

  ;; postulate sb
  (define-typed-variable sb 'sb ⇒ (-> (spy mb) ⊥))
  (check-type (spy mh) : Type)
  )

(define-datatype man : Type
  [o : man])

(with-link 'RB ([o mh] [o mb])
  o)

(with-link 'RB ([o mh] [o mb])
  ;(#%app- print- mh)
  (#%app- println- o)
  (check-type mh : man)
  (check-type o : man)
  (check-type man : Type)
  (check-type sh : (spy mh))
  o
  (#%app- println- (spy o))
  (spy o)
  )
