-- Adding Maybe to a Persuasion Algebra

open import PersuasionAlgebra

module PAMaybe {c ℓ₁ ℓ₂} {{pa : PersuasionAlgebra c ℓ₁ ℓ₂}} where

open import Algebra
open import Data.Maybe
open import Data.Product hiding (_<*>_)
open import Relation.Binary
-- open import Relation.Binary.Bundles using (Poset)
-- open import Relation.Binary.Core hiding (_⇒_)
-- open import Relation.Binary.Definitions
-- open import Relation.Binary.PropositionalEquality
-- open import Relation.Binary.Structures 

-- open import FuzzyMonad pa


MC = Maybe (Carrier)
-- MC⊥ = just (⊥)
MCε = just (ε)

private
  _<*>_ : ∀ {l} {A B : Set l} → Maybe (A → B) → Maybe A → Maybe B
  mf <*> mx = mf >>= λ f → mx >>= λ x → just (f x)

  infixl 4 _<*>_

CommMon : CommutativeMonoid c ℓ₁
CommMon = record
            { Carrier = Carrier
            ; _≈_ = _≈_
            ; _∙_ = _⊗_
            ; ε = ε
            ; isCommutativeMonoid = isCommutativeMonoid
            }

POrder : Poset c ℓ₁ ℓ₂
POrder = record
             { Carrier = Carrier
             ; _≈_ = _≈_
             ; _≤_ = _≤_
             ; isPartialOrder = isPartialOrder
             }

-- BoundLat : BoundedLattice c ℓ₁
-- BoundLat = record
--              { Carrier = Carrier
--              ; _≈_ = _≈_
--              ; _∙_ = _∧_
--              ; ε = ε
--              ; isIdempotentCommutativeMonoid = isBoundedLattice
--              }


data M-rel {c} {ℓ} {A : Set c} : Rel A ℓ → Rel (Maybe A) ℓ where
  mrel  : (r : Rel A ℓ) {x y : A} → r x y → M-rel r (just x) (just y)
  mreln : (r : Rel A ℓ) → M-rel r nothing nothing

M-op : ∀ {c} {A : Set c} → Op₂ A → Op₂ (Maybe A)
M-op op x y = just op <*> x <*> y

M-op₁ : ∀ {c} {A : Set c} → Op₁ A → Op₁ (Maybe A)
M-op₁ op x = just op <*> x 


infixl 10 _⟪⨂⟫_  -- _⟪⨁⟫⁺_

_⟪≈⟫_ = M-rel (_≈_)
_⟪≤⟫_ = M-rel (_≤_)

_⟪⨂⟫_ = M-op (_⊗_)
-- _⟪⇒⟫_ = M-op (_⇒_)
-- _⟪∧⟫_ = M-op (_∧_)
-- _⟪∨⟫_ = M-op (_∨_)

-- ⟪neg⟫ = M-op₁ (⊘)

-- the "or" version of ⟪∙⟫
-- _⟪_⟫⁺_ : MC → ((Carrier) → (Carrier) → (Carrier)) → MC → MC
-- just v1 ⟪ op ⟫⁺ just v2 = just (op v1 v2)
-- nothing ⟪ op ⟫⁺ just v2 = just v2
-- just v1 ⟪ op ⟫⁺ nothing = just v1
-- nothing ⟪ op ⟫⁺ nothing = nothing

-- _⟪⨁⟫⁺_ : MC → MC → MC
-- x ⟪⨁⟫⁺ y = x ⟪ _⊕_ ⟫⁺ y 





-- Tools for assessing Maybe versions of algebras

private
  M-assoc : ∀ {A : Set c} {eq : Rel A ℓ₁} {op : Op₂ A}
            → Associative eq op
            → Associative (M-rel eq) (M-op op)
  M-assoc {A} {eq} {op} assoc nothing y z = mreln eq
  M-assoc {A} {eq} {op} assoc (just x) nothing z = mreln eq
  M-assoc {A} {eq} {op} assoc (just x) (just x₁) nothing = mreln eq
  M-assoc {A} {eq} {op} assoc (just x) (just x₁) (just x₂) = mrel eq (assoc x x₁ x₂)
  
  M-comm : ∀ {A : Set c} {eq : Rel A ℓ₁} {op : Op₂ A}
           → Commutative eq op
           → Commutative (M-rel eq) (M-op op)
  M-comm {A} {eq} {op} comm nothing nothing = mreln eq
  M-comm {A} {eq} {op} comm nothing (just x) = mreln eq
  M-comm {A} {eq} {op} comm (just x) nothing = mreln eq
  M-comm {A} {eq} {op} comm (just x) (just x₁) = mrel eq (comm x x₁)
          
  M-identity : ∀ {A : Set c} {eq : Rel A ℓ₁} {top : A} {op : Op₂ A}
               → Identity eq top op
               → Identity (M-rel eq) (just top) (M-op op)
  M-identity {A} {eq} {top} {op} idn = ML , MR
    where
    ML : ∀ x → (M-rel eq) ((M-op op) (just top) x) x
    ML nothing = mreln eq
    ML (just x) = mrel eq (proj₁ idn x)
  
    MR : ∀ x → (M-rel eq) ((M-op op) x (just top)) x
    MR nothing = mreln eq
    MR (just x) = mrel eq (proj₂ idn x)
  
  M-cong : ∀ {A : Set c} {eq : Rel A ℓ₁} {op : Op₂ A} → Congruent₂ eq op → Congruent₂ (M-rel eq) (M-op op)
  M-cong {A} {eq} {op} cong {nothing} {nothing} m1 m2 = m1
  M-cong {A} {eq} {op} cong {just x} {just y} {nothing} {nothing} m1 m2 = m2
  M-cong {A} {eq} {op} cong {just x} {just y} {just u} {just v} (mrel .eq x₁) (mrel .eq x₂) = mrel eq (cong x₁ x₂)
  
  M-refl : ∀ {ℓ} {A : Set c} {eq : Rel A ℓ} → Reflexive eq → Reflexive (M-rel eq)
  M-refl {eq = eq} iseq {nothing} = mreln eq
  M-refl {eq = eq} iseq {just x} = mrel eq iseq

  M-sym : ∀ {ℓ} {A : Set c} {eq : Rel A ℓ} → Symmetric eq → Symmetric (M-rel eq)
  M-sym {eq = eq} iseq {nothing} {nothing} z = z
  M-sym {eq = eq} iseq {just x} {just x₁} (mrel .eq x₂) = mrel eq (iseq x₂)

  M-trans : ∀ {ℓ} {A : Set c} {eq : Rel A ℓ} → Transitive eq → Transitive (M-rel eq)
  M-trans {eq = eq} iseq {nothing} {nothing} {z} _ n = n
  M-trans {eq = eq} iseq {just x} {just x₁} {just x₂} (mrel .eq x₃) (mrel .eq x₄) = mrel eq (iseq x₃ x₄)
  
  M-isEquivalence : ∀ {A : Set c} {eq : Rel A ℓ₁} → IsEquivalence eq → IsEquivalence (M-rel eq)
  M-isEquivalence {A} {eq} iseq = record { refl = M-refl (IsEquivalence.refl iseq)
                                         ; sym = M-sym (IsEquivalence.sym iseq)
                                         ; trans = M-trans (IsEquivalence.trans iseq)
                                         }

  M-idem : ∀ {A : Set c} {eq : Rel A ℓ₁} {op : Op₂ A} → Idempotent eq op → Idempotent (M-rel eq) (M-op op)
  M-idem {A} {eq} {op} idem nothing = mreln eq
  M-idem {A} {eq} {op} idem (just x) = mrel eq (idem x)

  M-antisym : {A : Set c} {eq : Rel A ℓ₁} {r : Rel A ℓ₂}
              → Antisymmetric eq r → Antisymmetric (M-rel eq) (M-rel r)
  M-antisym {eq = eq} {r = r} isr {nothing} {nothing} _ _ = mreln eq
  M-antisym {eq = eq} {r = r} isr {just x} {just x₁} (mrel .r x₂) (mrel .r x₃) = mrel eq (isr x₂ x₃)
    
  
MCisCommutativeMonoid  : IsCommutativeMonoid _⟪≈⟫_ _⟪⨂⟫_ MCε 
MCisCommutativeMonoid = record
                        { isMonoid = record
                          { isSemigroup = record
                            { isMagma = record
                              { isEquivalence = M-isEquivalence (CommutativeMonoid.isEquivalence CommMon)
                              ; ∙-cong = M-cong (CommutativeMonoid.∙-cong CommMon)
                              }
                            ; assoc = M-assoc (CommutativeMonoid.assoc CommMon)
                            }
                          ; identity = M-identity (CommutativeMonoid.identity CommMon)
                          }
                        ; comm = M-comm (CommutativeMonoid.comm CommMon)
                        }

M-refl' : {A : Set c} {eq : Rel A ℓ₁} {r : Rel A ℓ₂} 
          → eq ⇒ r → (M-rel eq) ⇒ (M-rel r) 
M-refl' {A} {eq} {r} eq⇒r (mreln .eq) = mreln r
M-refl' {A} {eq} {r} eq⇒r (mrel .eq x) = mrel r (eq⇒r x)

MCisPartialOrder : IsPartialOrder _⟪≈⟫_ _⟪≤⟫_
MCisPartialOrder = record
                   { isPreorder = record
                     { isEquivalence = M-isEquivalence (Poset.isEquivalence POrder)
                     ; reflexive = M-refl' (Poset.reflexive POrder)
                     ; trans = M-trans (Poset.trans POrder)
                     }
                   ; antisym = M-antisym (Poset.antisym POrder)
                   }

MCisPersuasionAlgebra : IsPersuasionAlgebra _⟪≈⟫_ _⟪≤⟫_ _⟪⨂⟫_ MCε
MCisPersuasionAlgebra = record { isPartialOrder = MCisPartialOrder 
                               ; isCommutativeMonoid = MCisCommutativeMonoid
                               }

open import WLPretty

docMC : MC → Doc
docMC nothing  = text "Nothing"
docMC (just x) = text "Just " <> (doc) x

instance
  ppMC : Pretty MC
  pretty {{ppMC}} = docMC
  pppMC : PPrint MC
  prettytype {{pppMC}} = ppMC


MRL : PersuasionAlgebra _ _ _
MRL = record
  { Carrier = MC
  ; _≈_ = _⟪≈⟫_
  ; _≤_ = M-rel (_≤_)
  ; _⊗_ = _⟪⨂⟫_
  ; ε = MCε
  ; isPersuasionAlgebra = MCisPersuasionAlgebra
  ; doc = docMC
  }

