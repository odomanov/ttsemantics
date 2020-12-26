-- Adding Maybe to a Persuasion Algebra

open import PersuasionAlgebra

module PAMaybe {c ℓ₁ ℓ₂} {{pa : PersuasionAlgebra c ℓ₁ ℓ₂}} where

open import Algebra renaming (CommutativeMonoid to CM)
open import Data.Maybe
open import Data.Product hiding (_<*>_)
open import Relation.Binary


MC = Maybe (Carrier)
MCε = just (ε)

-- Maybe monad operation <*>.

private
  _<*>_ : ∀ {l} {A B : Set l} → Maybe (A → B) → Maybe A → Maybe B
  mf <*> mx = mf >>= λ f → mx >>= λ x → just (f x)

  infixl 4 _<*>_

CommMon : CM c ℓ₁
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


-- Adding Maybe to relations and operations.

data M-rel {c} {ℓ} {A : Set c} : Rel A ℓ → Rel (Maybe A) ℓ where
  mreln : (r : Rel A ℓ) → M-rel r nothing nothing
  mrel  : (r : Rel A ℓ) {x y : A} → r x y → M-rel r (just x) (just y)

M-op₂ : ∀ {c} {A : Set c} → Op₂ A → Op₂ (Maybe A)
M-op₂ op x y = just op <*> x <*> y

M-op₁ : ∀ {c} {A : Set c} → Op₁ A → Op₁ (Maybe A)
M-op₁ op x = just op <*> x 


infixl 10 _⟪⨂⟫_  -- _⟪⨁⟫⁺_

_⟪≈⟫_ = M-rel (_≈_)
_⟪≤⟫_ = M-rel (_≤_)

_⟪⨂⟫_ = M-op₂ (_⊗_)




-- Auxiliary functions for assessing Maybe versions of algebras

private
  M-assoc : ∀ {A : Set c} {eq : Rel A ℓ₁} {op : Op₂ A}
            → Associative eq op
            → Associative (M-rel eq) (M-op₂ op)
  M-assoc {eq = eq} assoc nothing y z = mreln eq
  M-assoc {eq = eq} assoc (just x) nothing z = mreln eq
  M-assoc {eq = eq} assoc (just x) (just x₁) nothing = mreln eq
  M-assoc {eq = eq} assoc (just x) (just x₁) (just x₂) = mrel eq (assoc x x₁ x₂)
  
  M-comm : ∀ {A : Set c} {eq : Rel A ℓ₁} {op : Op₂ A}
           → Commutative eq op
           → Commutative (M-rel eq) (M-op₂ op)
  M-comm {eq = eq} comm nothing nothing = mreln eq
  M-comm {eq = eq} comm nothing (just x) = mreln eq
  M-comm {eq = eq} comm (just x) nothing = mreln eq
  M-comm {eq = eq} comm (just x) (just x₁) = mrel eq (comm x x₁)
          
  M-identity : ∀ {A : Set c} {eq : Rel A ℓ₁} {top : A} {op : Op₂ A}
               → Identity eq top op
               → Identity (M-rel eq) (just top) (M-op₂ op)
  M-identity {A} {eq} {top} {op} idn = ML , MR
    where
    ML : ∀ x → (M-rel eq) ((M-op₂ op) (just top) x) x
    ML nothing  = mreln eq
    ML (just x) = mrel eq (proj₁ idn x)
  
    MR : ∀ x → (M-rel eq) ((M-op₂ op) x (just top)) x
    MR nothing  = mreln eq
    MR (just x) = mrel eq (proj₂ idn x)
  
  M-cong : ∀ {A : Set c} {eq : Rel A ℓ₁} {op : Op₂ A}
           → Congruent₂ eq op
           → Congruent₂ (M-rel eq) (M-op₂ op)
  M-cong           cong {nothing} {nothing} m1 _ = m1
  M-cong           cong {just _} {just _} {nothing} {nothing} _ m2 = m2
  M-cong {eq = eq} cong (mrel .eq x₁) (mrel .eq x₂) = mrel eq (cong x₁ x₂)
  
  M-refl : ∀ {ℓ} {A : Set c} {eq : Rel A ℓ} → Reflexive eq → Reflexive (M-rel eq)
  M-refl {eq = eq} iseq {nothing} = mreln eq
  M-refl {eq = eq} iseq {just x} = mrel eq iseq

  M-sym : ∀ {ℓ} {A : Set c} {eq : Rel A ℓ} → Symmetric eq → Symmetric (M-rel eq)
  M-sym           iseq {nothing} {nothing} z = z
  M-sym {eq = eq} iseq (mrel .eq x) = mrel eq (iseq x)

  M-trans : ∀ {ℓ} {A : Set c} {eq : Rel A ℓ} → Transitive eq → Transitive (M-rel eq)
  M-trans           iseq {nothing} {nothing} {z} _ n = n
  M-trans {eq = eq} iseq (mrel .eq x) (mrel .eq y) = mrel eq (iseq x y)
  
  M-isEquivalence : ∀ {A : Set c} {eq : Rel A ℓ₁} → IsEquivalence eq → IsEquivalence (M-rel eq)
  M-isEquivalence iseq = record { refl = M-refl (IsEquivalence.refl iseq)
                                ; sym = M-sym (IsEquivalence.sym iseq)
                                ; trans = M-trans (IsEquivalence.trans iseq)
                                }

  M-idem : {A : Set c} {eq : Rel A ℓ₁} {op : Op₂ A}
           → Idempotent eq op
           → Idempotent (M-rel eq) (M-op₂ op)
  M-idem {eq = eq} idem nothing = mreln eq
  M-idem {eq = eq} idem (just x) = mrel eq (idem x)

  M-antisym : {A : Set c} {eq : Rel A ℓ₁} {r : Rel A ℓ₂}
              → Antisymmetric eq r
              → Antisymmetric (M-rel eq) (M-rel r)
  M-antisym {eq = eq} {r = r} isr {nothing} {nothing} _ _ = mreln eq
  M-antisym {eq = eq} {r = r} isr (mrel .r x) (mrel .r y) = mrel eq (isr x y)
    
  
MCisCommutativeMonoid  : IsCommutativeMonoid _⟪≈⟫_ _⟪⨂⟫_ MCε 
MCisCommutativeMonoid = record
                        { isMonoid = record
                          { isSemigroup = record
                            { isMagma = record
                              { isEquivalence = M-isEquivalence (CM.isEquivalence CommMon)
                              ; ∙-cong = M-cong (CM.∙-cong CommMon)
                              }
                            ; assoc = M-assoc (CM.assoc CommMon)
                            }
                          ; identity = M-identity (CM.identity CommMon)
                          }
                        ; comm = M-comm (CM.comm CommMon)
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

-- Pretty printing

open import WLPretty

docMC : MC → Doc
docMC nothing  = text "Nothing"
docMC (just x) = text "Just " <> (doc) x

instance
  ppMC : Pretty MC
  pretty {{ppMC}} = docMC
  pppMC : PPrint MC
  prettytype {{pppMC}} = ppMC



-- Persuasion Algebra with Maybe values

MCPA : PersuasionAlgebra _ _ _
MCPA = record
  { Carrier = MC
  ; _≈_ = _⟪≈⟫_
  ; _≤_ = _⟪≤⟫_
  ; _⊗_ = _⟪⨂⟫_
  ; ε = MCε
  ; isPersuasionAlgebra = MCisPersuasionAlgebra
  ; doc = docMC
  }

