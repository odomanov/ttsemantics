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
           rackunit/turnstile
           cur/stdlib/sugar)
  (provide man mh mb spy sh sb)
  (define-datatype man : Type
    [mh : man] [mb : man])
  (define-datatype spymh : Type
    [sh : spymh])
  (define spymb ⊥)
  (define/rec/match spy : man -> Type
    [mh => spymh]
    [mb => spymb])
  (check-type (spy mh) : Type)
  
  (define/rec/match sb : spymb -> ⊥)
  (check-type (spy mh) : Type)
  )

(define-datatype man : Type
  [o : man])

(with-link 'RB ([o mh] [o mb])
  o)

(with-link 'RB ([o mh] [o mb])
  (spy o))

