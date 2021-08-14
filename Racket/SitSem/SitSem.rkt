;; modified cur (lang.rkt), this is basically just cic-saccharata
#lang racket/base

(provide ;; #%module-begin
 provide require for-syntax
 all-from-out rename-out except-out all-defined-out
 only-in except-in
 begin-for-syntax
 module+
 module*
 module
 submod
 ;; define-values begin define #%app λ
 #%plain-app void #%plain-lambda printf displayln quote begin
 define-syntax define-for-syntax
 (for-syntax
  (all-from-out racket/base
                syntax/parse
                racket/syntax)))

(require (for-syntax racket/base syntax/parse racket/syntax))

(require (only-in turnstile+/base
                  define-typed-syntax syntax-parse/typecheck get-orig assign-type
                  define-typed-variable-syntax current-typecheck-relation
                  current-check-relation
                  subst substs typecheck? typechecks? typeof add-expected-type
                  current-type-eval expand/df typecheck-fail-msg/multi
                  type-error
                  ⇒ ⇐ ≫ ⊢ ≻)
         turnstile+/eval
         turnstile+/typedefs
         (for-syntax macrotypes/stx-utils syntax/stx
                     (for-syntax racket/base syntax/parse)))
(provide (all-from-out turnstile+/base turnstile+/eval turnstile+/typedefs))

(require cur/curnel/cic-saccharata)
(provide (all-from-out cur/curnel/cic-saccharata))

(require (for-syntax "link.rkt"))
(provide (for-syntax (all-from-out "link.rkt")))

(define-syntax (#%datum syn)
  (raise-syntax-error
   '#%datum
   "No datum parser defined"
   syn))

(provide #%datum)
