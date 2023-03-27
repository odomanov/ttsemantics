-- Automatic derivation of decidable equality for some inductive types. 
-- Cf. https://github.com/alhassy/gentle-intro-to-reflection.
-- Tested on: Agda version Agda version 2.6.3-b499d12, std-lib 1.7.2

module _ where

open import Data.Bool using (true; false)
open import Data.List using (List; _∷_; []; map; mapMaybe; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_) -- (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary --using (Dec; yes; no) --renaming (no to not)
open import Level renaming (zero to lzero; suc to lsuc)

open import Agda.Builtin.Reflection
open import Reflection


-- Preparation
-- ===========

constructors : Definition → List Name
constructors (data-type pars cs) = cs
constructors _ = []

vra0 : {A : Set} → A → Arg A
vra0 = arg (arg-info visible (modality relevant quantity-0))

hra0 : {A : Set} → A → Arg A
hra0 = arg (arg-info hidden (modality relevant quantity-0))

vra : {A : Set} → A → Arg A
vra = arg (arg-info visible (modality relevant quantity-ω))

hra : {A : Set} → A → Arg A
hra = arg (arg-info hidden (modality relevant quantity-ω))

-- hetero map
map2 : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
       → (A → B → C) → List A → List B → List C
map2 f [] _ = []
map2 f _ [] = []
map2 f (x ∷ xs) l = map (f x) l ++ map2 f xs l 

-- skip when the result is 'nothing'
map2Maybe : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
            → (A → B → Maybe C) → List A → List B → List C
map2Maybe f [] _ = []
map2Maybe f _ [] = []
map2Maybe f (x ∷ xs) l = mapMaybe (f x) l ++ map2Maybe f xs l 

mk-cls : Name → Name → Term → Clause
mk-cls q1 q2 rhs = clause [] (vra (con q1 []) ∷ vra (con q2 []) ∷ []) rhs


-- Decidable equality. Simple types (including dependent).
-- =======================================================

mk-cls-dec-eq : Name → Name → Name → Clause
mk-cls-dec-eq ty q1 q2 with primQNameEquality q1 q2
... | true  = mk-cls q1 q2 (con (quote _because_)
                           (vra (con (quote true) []) ∷
                            vra (con (quote ofʸ) (vra (con (quote refl) []) ∷ [])) ∷
                            []))
... | false = mk-cls q1 q2 (con (quote _because_)
                           (vra (con (quote false) []) ∷
                            vra (con (quote ofⁿ)
                                     (vra (pat-lam (absurd-clause absurd-tel
                                                                  (vra (absurd 0) ∷ []) ∷
                                                    []) []) ∷
                                      [])) ∷
                            []))
  where
  ≡-type : Type
  ≡-type = def (quote _≡_) ( hra (def (quote lzero) [])
                           ∷ hra (def ty [])
                           ∷ vra (con q1 [])
                           ∷ vra (con q2 [])
                           ∷ [])
  absurd-tel : Telescope
  absurd-tel = ("()" , vra ≡-type) ∷ []

defDecEq : Name → Name → TC ⊤
defDecEq ty nom = do
       δ ← getDefinition ty 
       let constrs = constructors δ
       let clauses = map2 (mk-cls-dec-eq ty) constrs constrs
       defineFun nom clauses


-- Boolean equality. Simple types (including dependent).
-- =====================================================

mk-cls-bool-eq : Name → Name → Clause
mk-cls-bool-eq q1 q2 with primQNameEquality q1 q2
... | true  = mk-cls q1 q2 (con (quote true)  [])
... | false = mk-cls q1 q2 (con (quote false) [])

defBoolEq : Name → Name → TC ⊤
defBoolEq ty nom = do
       δ ← getDefinition ty
       let constrs = constructors δ
       let clauses = map2 mk-cls-bool-eq constrs constrs
       defineFun nom clauses



-- Boolean equality. More complicated types.
-- =========================================

-- mk-cls-bool-eq2 : Name → Name → Maybe Clause
-- mk-cls-bool-eq2 (quote val) q2 = nothing
-- mk-cls-bool-eq2 q1 (quote val) = nothing
-- mk-cls-bool-eq2 q1 q2 with primQNameEquality q1 q2
-- ... | true  = just (mk-cls q1 q2 (con (quote true)  []))
-- ... | false = just (mk-cls q1 q2 (con (quote false) []))

-- mk-cls-bool-eq-v : Name → Name → Clause
-- mk-cls-bool-eq-v q1 q2 = clause (("x" , (vra (def (quote Typ) []))) ∷ 
--                                  ("y" , (vra (def (quote Typ) []))) ∷
--                                  [])
--                         (vra (con (quote val) (vra (var 1) ∷ vra (con q1 []) ∷ [])) ∷ 
--                          vra (con (quote val) (vra (var 0) ∷ vra (con q2 []) ∷ [])) ∷
--                          [])
--                         (def (quote _==_) (vra (con q1 []) ∷ (vra (con q2 []) ∷ [])))
-- -- mk-cls-bool-eq-v q1 q2 with primQNameEquality q1 q2
-- -- ... | true  = clause [] (vra (con (quote val) (vra (con q1 []) ∷ [])) ∷ 
-- --                          vra (con (quote val) (vra (con q2 []) ∷ [])) ∷ [])
-- --                         (con (quote true)  [])
-- -- ... | false = clause [] (vra (con (quote val) (vra (con q1 []) ∷ [])) ∷ 
-- --                          vra (con (quote val) (vra (con q2 []) ∷ [])) ∷ [])
-- --                         (con (quote false) [])

-- defBoolEq3 : Name → TC ⊤
-- defBoolEq3 ty argty nom = do
--        δ ← getDefinition ty    --(quote QQQ)
--        v ← getDefinition argty --(quote Val)
--        let constrs-δ = constructors δ
--        let constrs-v = constructors v
--        let clauses1 = map2Maybe mk-cls-bool-eq2 constrs-δ constrs-δ
--        let clauses2 = map2 mk-cls-bool-eq-v constrs-v constrs-v
--        let clauses3 = clause (("x" , (vra (def ty []))) ∷ 
--                               ("y" , (vra (def ty []))) ∷ [])
--                              ((vra (var 1)) ∷ vra (var 0) ∷ [])
--                              (con (quote false) []) ∷ []
--        let clauses = clauses1 ++ clauses2 ++ clauses3
--        -- ty ← quoteTC (QQQ → QQQ → Bool)
--        -- declareDef (vra nom) ty
--        defineFun nom clauses

-- -- Example

-- data QQQ : Set where
--   pp qq : QQQ
--   val   : (A : Typ) → Val A → QQQ


-- eqBool3 : QQQ → QQQ → Bool
-- unquoteDef eqBool3 = defBoolEq3 (quote QQQ) (quote Val) eqBool3
-- -- unquoteDecl eqBool3 = ddef3 eqBool3

-- _ : eqBool3 pp pp ≡ true
-- _ = refl

-- _ : eqBool3 (val _ a1) (val _ a1) ≡ true
-- _ = refl

-- _ : eqBool3 (val AA a1) (val _ a2) ≡ false
-- _ = refl

-- -- _ : eqBool3 (val a1) (val pp) ≡ false
-- -- _ = refl

-- _ : eqBool3 pp (val _ a1) ≡ false
-- _ = refl

-- _ : eqBool3 (val BB b1) qq ≡ false
-- _ = refl
