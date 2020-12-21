-- Adding Maybe to a Residuated Lattice

open import ResiduatedLattice

module RLMaybe {c ℓ₁ ℓ₂} (la : ResiduatedLattice c ℓ₁ ℓ₂) where

open import Algebra
open import Data.Maybe
open import Data.Product hiding (_<*>_)
open import Relation.Binary.Core hiding (_⇒_)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Structures 

-- open import FuzzyMonad la


MC = Maybe (Carrier la)
MC⊥ = just (⊥ la)
MC⊤ = just (⊤ la)

private
  _<*>_ : ∀ {l} {A B : Set l} → Maybe (A → B) → Maybe A → Maybe B
  mf <*> mx = mf >>= λ f → mx >>= λ x → just (f x)

  infixl 4 _<*>_

  CommMon : CommutativeMonoid c ℓ₁
  CommMon = record
              { Carrier = Carrier la
              ; _≈_ = _≈_ la
              ; _∙_ = _⊗_ la
              ; ε = ⊤ la
              ; isCommutativeMonoid = isCommutativeMonoid la
              }
  
  BoundLat : BoundedLattice c ℓ₁
  BoundLat = record
               { Carrier = Carrier la
               ; _≈_ = _≈_ la
               ; _∙_ = _∧_ la
               ; ε = ⊤ la
               ; isIdempotentCommutativeMonoid = isBoundedLattice la
               }


data M-rel {c} {ℓ} {A : Set c} : Rel A ℓ → Rel (Maybe A) ℓ where
  mrel  : (r : Rel A ℓ) {x y : A} → r x y → M-rel r (just x) (just y)
  mreln : (r : Rel A ℓ) → M-rel r nothing nothing

M-op : ∀ {c} {A : Set c} → Op₂ A → Op₂ (Maybe A)
M-op op x y = just op <*> x <*> y

M-op₁ : ∀ {c} {A : Set c} → Op₁ A → Op₁ (Maybe A)
M-op₁ op x = just op <*> x 


infixl 10 _⟪⨂⟫_  -- _⟪⨁⟫⁺_

_⟪≈⟫_ = M-rel (_≈_ la)

_⟪⨂⟫_ = M-op (_⊗_ la)
_⟪⇒⟫_ = M-op (_⇒_ la)
_⟪∧⟫_ = M-op (_∧_ la)
_⟪∨⟫_ = M-op (_∨_ la)

-- ⟪neg⟫ = M-op₁ (⊘ la)

-- the "or" version of ⟪∙⟫
-- _⟪_⟫⁺_ : MC → ((Carrier la) → (Carrier la) → (Carrier la)) → MC → MC
-- just v1 ⟪ op ⟫⁺ just v2 = just (op v1 v2)
-- nothing ⟪ op ⟫⁺ just v2 = just v2
-- just v1 ⟪ op ⟫⁺ nothing = just v1
-- nothing ⟪ op ⟫⁺ nothing = nothing

-- _⟪⨁⟫⁺_ : MC → MC → MC
-- x ⟪⨁⟫⁺ y = x ⟪ _⊕_ la ⟫⁺ y 





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
  
  M-isEquivalence : ∀ {A : Set c} {eq : Rel A ℓ₁} → IsEquivalence eq → IsEquivalence (M-rel eq)
  M-isEquivalence {A} {eq} iseq = record { refl = M-refl (IsEquivalence.refl iseq)
                                         ; sym = M-sym (IsEquivalence.sym iseq)
                                         ; trans = M-trans (IsEquivalence.trans iseq)
                                         }
    where
    M-refl : Reflexive eq → Reflexive (M-rel eq)
    M-refl iseq {nothing} = mreln eq
    M-refl iseq {just x} = mrel eq iseq
  
    M-sym : Symmetric eq → Symmetric (M-rel eq)
    M-sym iseq {nothing} {nothing} z = z
    M-sym iseq {just x} {just x₁} (mrel .eq x₂) = mrel eq (iseq x₂)
  
    M-trans : Transitive eq → Transitive (M-rel eq)
    M-trans iseq {nothing} {nothing} {z} _ n = n
    M-trans iseq {just x} {just x₁} {just x₂} (mrel .eq x₃) (mrel .eq x₄) = mrel eq (iseq x₃ x₄)
  
  M-idem : ∀ {A : Set c} {eq : Rel A ℓ₁} {op : Op₂ A} → Idempotent eq op → Idempotent (M-rel eq) (M-op op)
  M-idem {A} {eq} {op} idem nothing = mreln eq
  M-idem {A} {eq} {op} idem (just x) = mrel eq (idem x)

MCisCommutativeMonoid  : IsCommutativeMonoid _⟪≈⟫_ _⟪⨂⟫_ MC⊤ 
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


MCisBoundedLattice : IsBoundedLattice _⟪≈⟫_ _⟪∧⟫_ MC⊤
MCisBoundedLattice = record
                     { isCommutativeMonoid = record
                       { isMonoid = record
                         { isSemigroup = record
                           { isMagma = record
                             { isEquivalence = M-isEquivalence (BoundedLattice.isEquivalence BoundLat)
                             ; ∙-cong = M-cong (BoundedLattice.∙-cong BoundLat)
                             }
                           ; assoc = M-assoc (BoundedLattice.assoc BoundLat)
                           }
                         ; identity = M-identity (BoundedLattice.identity BoundLat)
                         }
                       ; comm = M-comm (BoundedLattice.comm BoundLat)
                       }
                     ; idem = M-idem (BoundedLattice.idem BoundLat)
                     }

MCisResiduatedLattice : IsResiduatedLattice _⟪≈⟫_ (M-rel (_≤_ la))
                        _⟪⨂⟫_ (M-op (_⇒_ la)) _ (M-op (_∨_ la)) MC⊤ MC⊥
MCisResiduatedLattice = record { isBoundedLattice = MCisBoundedLattice
                               ; isCommutativeMonoid = MCisCommutativeMonoid
                               }
