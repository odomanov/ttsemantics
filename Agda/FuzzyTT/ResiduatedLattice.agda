-- ResiduatedLattice is a superclass of PersuasionAlgebra

module ResiduatedLattice where

open import Level
open import Algebra
open import Data.Product
open import Relation.Binary hiding (_⇒_)

open import WLPretty

open import PersuasionAlgebra

record IsResiduatedLattice {c ℓ₁ ℓ₂} {A : Set c}
                         (_≈_ : Rel A ℓ₁)
                         (_≤_ : Rel A ℓ₂)
                         (_⊗_ : Op₂ A)
                         (_⇒_ : Op₂ A)
                         (_∧_ : Op₂ A)
                         (_∨_ : Op₂ A)
                         (⊤ : A)
                         (⊥ : A)
                         : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    isPersuasionAlgebra  : IsPersuasionAlgebra _≈_ _≤_ _⊗_ ⊤
    isBoundedLattice     : IsBoundedLattice _≈_ _∧_ ⊤ 

  -- TODO define ⇒ 

record ResiduatedLattice c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  constructor mkResiduatedLattice
  field
    {{persuasionAlgebra}} : PersuasionAlgebra c ℓ₁ ℓ₂ 
    _⇒_     : Op₂ Carrier     -- The residuum
    _∧_     : Op₂ Carrier     -- The minimum operation.
    _∨_     : Op₂ Carrier     -- The maximum operation.
    ⊤       : Carrier         -- The maximum.
    ⊥       : Carrier         -- The minimum.
    isResiduatedLattice : IsResiduatedLattice _≈_ _≤_ _⊗_ _⇒_ _∧_ _∨_ ⊤ ⊥ 
    doc : Carrier → Doc
    
  open IsResiduatedLattice isResiduatedLattice public

open ResiduatedLattice public


instance
  RLtoPA : ∀ {c ℓ₁ ℓ₂} → toPA c ℓ₁ ℓ₂ (ResiduatedLattice c ℓ₁ ℓ₂)
  RLtoPA {c} {ℓ₁} {ℓ₂}= topa persuasionAlgebra
