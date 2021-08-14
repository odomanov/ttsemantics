#lang cur
(require
  ;cur/stdlib/sugar
  cur/stdlib/axiom
  cur/stdlib/sigma
  ;cur/stdlib/prop
  cur/stdlib/list
  ;cur/stdlib/equality
  ;"cur-more.rkt"
  ;cur/curnel/cic-saccharata
  rackunit/turnstile+
  ;"rackunit-ntac.rkt"
  rackunit/private/check
  )


(module common cur
  (provide ⊥ ⊤ ¬)
  (data ⊥ : 0 Type)
  (data ⊤ : 0 Type
        [tt : ⊤])

  (define-typed-syntax (¬ τ) ≫
    [⊢ τ ≫ τ- ⇒ (~Type _)]
    --------
    [≻ (-> τ ⊥)])
  )

(require 'common)

;; Ralph's belief
;; --------------

(module RB cur
  (require
    (submod ".." common)
    ;cur/stdlib/sugar
    cur/stdlib/axiom
    cur/stdlib/sigma
    ;cur/stdlib/prop
    ;"cur-more.rkt"
    rackunit/turnstile+)
  (provide man mh mb spy sh sb)
  (data man : 0 Type
        [mh : man]
        [mb : man])

  (define-axiom spy (-> man Type))
  (define-axiom sh (spy mh))
  (check-type (spy mh) : Type)
  ;(cur-type-check? (spy mh) Type)   ;unbound?

  (define-axiom sb (¬ (spy mb)))
  (check-type (spy mb) : Type)
  (check-type (¬ (spy mb)) : Type)
  (check-type sb : (¬ (spy mb)))
  (check-type sb : (-> (spy mb) ⊥))

  (define ¬spy (λ [m : man] (¬ (spy m))))
  (check-type sb : (¬spy mb))

  (define ¬spy-mb (-> (spy mb) ⊥))
  (define-axiom sb2 ¬spy-mb)
  (check-type sb2 : ¬spy-mb)
  (check-type sb2 : (¬ (spy mb)))
  (check-type sb2 : (-> (spy mb) ⊥))

  ;; some proofs
  (check-type (pair  spy mh sh)  : (Σ man spy))
  (check-type (pair ¬spy mb sb)  : (Σ man ¬spy))
  (check-type (pair ¬spy mb sb2) : (Σ man ¬spy))
  (check-type (pair (λ [m : man] (¬ (spy m))) mb sb) : (Σ man (λ [m : man] (¬ (spy m)))))

  )

(provide man o spy
         RB.man RB.mh RB.mb RB.sh RB.sb RB.spy)

(data man : 0 Type
      [o : man])
(define-axiom spy (-> man Type))
;(require racket)(syntax-debug-info #'o)
#;(begin-for-syntax
    (printf "info=~a\n" (get-datatype-info #'man))
    )


(require syntax/parse/define)

(define-syntax (require-situation stx)
  (syntax-parse stx
    [(_ sit)
     #:with prefix (format-id #'sit "~a." (cadr (syntax->datum #'sit)))
     #'(require (prefix-in prefix sit))]))

(require-situation 'RB)

;(require (prefix-in RB. 'RB))

#;(begin-for-syntax
  (require racket/pretty)
  (pretty-print (syntax-property-symbol-keys #'RB.mh))
  (pretty-print (syntax-property-symbol-keys #'o))
  (pretty-print (syntax-property-symbol-keys #''RB))
  )


;; counterparts via functions
;; ==========================

;(data c.man : 0 Type
;      [c.mh : c.man]
;      [c.mb : c.man])
;
;(define/rec/match c->W : c.man -> man
;  [c.mh => o]
;  [c.mb => o])
;
;(define/rec/match c->R : c.man -> RB.man
;  [c.mh => RB.mh]
;  [c.mb => RB.mb])
;
;
;(require cur/stdlib/nat)
;
;; non-empty list
;(data List1 : 1 (Π (A : Type) Type)
;      (nil1  : (Π (A : Type) [x : A] (List1 A)))
;      (cons1 : (Π (A : Type) [x : A] [xs : (List1 A)] (List1 A))))
;
;(define-syntax (lst1 syn)
;  (syntax-parse syn
;    [(_ A e)
;     #'(nil1 A e)]
;    [(_ A e e^ ...)
;     #'(cons1 A e (lst1 A e^ ...))]))
;
;(define/rec/match list1-ref : [A : Type] [n : Nat] (List1 A) -> A
;  [(nil1 B a) => a]
;  [(cons1 B a rst) => (match n #:return A
;                        [z a]
;                        [(s n-1) (list1-ref A n-1 rst)])])
;
;(define/rec/match fst1 : [A : Type] (List1 A) -> A
;  [(nil1 B a) => a]
;  [(cons1 B a _) => a])  
;
;
;(define/rec/match W->R : man -> (List1 RB.man)
;  [o => (lst1 RB.man RB.mh RB.mb)])
;
;(define/rec/match R->W : RB.man -> (List1 man)
;  [RB.mh => (lst1 man o)]
;  [RB.mb => (lst1 man o)])
;
;(check-equal? (R->W RB.mh) (nil1 man o))
;(check-equal? (R->W RB.mh) (lst1 man o))
;(check-equal? (W->R o)  (cons1 RB.man RB.mh (nil1 RB.man RB.mb)))
;(check-type (List1 RB.man) : Type)
;(check-type (W->R o) : (List1 RB.man))
;
;;; Ralph believes that Ortcutt is a spy
;(check-type RB.sh : (RB.spy (fst1 RB.man (W->R o))))
;
;(data OR : 2 (Π [A : Type] [B : Type] Type)
;      [orl : (Π (A : Type) (B : Type) (a : A) (OR A B))]
;      [orr : (Π (A : Type) (B : Type) (b : B) (OR A B))])
;(define/rec/match ormap1 : [A : Type] (f : (-> A Type)) (List1 A) -> Type
;  [(nil1 B a) => (f a)]
;  [(cons1 B a rst) => (OR (f a) (ormap1 A f rst))])
;
;(check-type
; (orl (== (RB.man) (RB.mh) (RB.mh)) (== (RB.man) (RB.mb) (RB.mh))
;      (refl RB.man RB.mh))
; : (ormap1 RB.man (λ (x : RB.man) (== x RB.mh)) (W->R o)))
;(check-type
; (refl man o)
; : (ormap1 man (λ (x : man) (== x o)) (R->W RB.mh)))
;
;;; o's counterparts
;(define cpo
;  (Σ RB.man
;     (λ [x : RB.man] (ormap1 RB.man (λ [y : RB.man] (== y x)) (W->R o)))))
;
;(check-type
; (pair (λ [x : RB.man] (ormap1 RB.man (λ [y : RB.man] (== y x)) (W->R o)))
;       RB.mh
;       (orl (== (RB.man) (RB.mh) (RB.mh)) (== (RB.man) (RB.mb) (RB.mh)) (refl RB.man RB.mh)))
; : cpo)
;
;;; there is an o's counterpart who is a spy
;(check-type
; (pair (λ [x : cpo] (RB.spy (fst x)))
;       (pair (λ [x : RB.man] (ormap1 RB.man (λ [y : RB.man] (== y x)) (W->R o)))
;             RB.mh
;             (orl (== (RB.man) (RB.mh) (RB.mh)) (== (RB.man) (RB.mb) (RB.mh)) (refl RB.man RB.mh)))
;       RB.sh)
; : (Σ cpo (λ [x : cpo] (RB.spy (fst x)))))
;
;;; there is an o's counterpart who is not a spy
;(check-type
; (pair (λ [x : cpo] (¬ (RB.spy (fst x))))
;       (pair (λ [x : RB.man] (ormap1 RB.man (λ [y : RB.man] (== y x)) (W->R o)))
;             RB.mb
;             (orr (== (RB.man) (RB.mh) (RB.mb)) (== (RB.man) (RB.mb) (RB.mb)) (refl RB.man RB.mb)))
;       RB.sb)
; : (Σ cpo (λ [x : cpo] (¬ (RB.spy (fst x))))))



;; counterparts via relations
;; ==========================


(data cp-rel : 0 (Π man RB.man Type)
      [omh : (cp-rel o RB.mh)]
      [omb : (cp-rel o RB.mb)])

;; o's counterparts
(define cpo2
  (Σ RB.man (λ [x : RB.man] (cp-rel o x))))

(check-type
 (pair (λ [x : RB.man] (cp-rel o x))
       RB.mh omh) : cpo2)

;; there is an o's counterpart (cpo is not empty)
(check-type
 (pair (λ [x : RB.man] (cp-rel o x)) RB.mh omh)
 : cpo2)

;; there is an o's counterpart who is a spy
(check-type
 (pair (λ [x : cpo2] (RB.spy (fst x)))
       (pair (λ [x : RB.man] (cp-rel o x))
             RB.mh
             omh)
       RB.sh)
 : (Σ cpo2 (λ [x : cpo2] (RB.spy (fst x)))))

;;; there is an o's counterpart who is not a spy
(check-type
 (pair (λ [x : cpo2] (¬ (RB.spy (fst x))))
       (pair (λ [x : RB.man] (cp-rel o x))
             RB.mb
             omb)
       RB.sb)
 : (Σ cpo2 (λ [x : cpo2] (¬ (RB.spy (fst x))))))



;;  Another variant

(data REL : 2 (Π (A : Type) (B : Type) Type)
      [rel : (Π (A : Type) (B : Type) (a : A) (b : B) (REL A B))])

(define cp-rel3 (REL man RB.man))
(define omh3 (rel man RB.man o RB.mh))
(define omb3 (rel man RB.man o RB.mb))

(check-type omh3 : cp-rel3)

;; o's counterparts
(define cpo3
  (Σ RB.man (λ [x : RB.man] cp-rel3)))

;; there is an o's counterpart (cpo is not empty)
(check-type (pair (λ [x : RB.man] cp-rel3)
                  RB.mh omh3)
            : cpo3)

;; there is an o's counterpart who is a spy
(check-type
 (pair (λ [x : cpo3] (RB.spy (fst x)))
       (pair (λ [x : RB.man] cp-rel3)
             RB.mh
             omh3)
       RB.sh)
 : (Σ cpo3 (λ [x : cpo3] (RB.spy (fst x)))))

;;; there is an o's counterpart who is not a spy
(check-type
 (pair (λ [x : cpo3] (¬ (RB.spy (fst x))))
       (pair (λ [x : RB.man] cp-rel3)
             RB.mb
             omb3)
       RB.sb)
 : (Σ cpo3 (λ [x : cpo3] (¬ (RB.spy (fst x))))))



;; The best version (presumably)
;; -----------------------------

(data cpWR : 0 Type
      [cp : (Π [xw : man] [xr : RB.man] cpWR)])  ;establishing connection
(define omh4 (cp o RB.mh))
(define omb4 (cp o RB.mb))

(check-type omb4 : cpWR)

;; o's counterparts
(define cpo4
  (Σ RB.man (λ [x : RB.man] cpWR)))

;; there is an o's counterpart (cpo is not empty)
(check-type (pair (λ [x : RB.man] cpWR)
                  RB.mh omh4)
            : cpo4)

;; there is an o's counterpart who is a spy
(check-type
 (pair (λ [x : cpo4] (RB.spy (fst x)))
       (pair (λ [x : RB.man] cpWR) RB.mh omh4)
       RB.sh)
 : (Σ cpo4 (λ [x : cpo4] (RB.spy (fst x)))))

;;; there is an o's counterpart who is not a spy
(check-type
 (pair (λ [x : cpo4] (¬ (RB.spy (fst x))))
       (pair (λ [x : RB.man] cpWR) RB.mb omb4)
       RB.sb)
 : (Σ cpo4 (λ [x : cpo4] (¬ (RB.spy (fst x))))))

