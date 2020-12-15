module ResiduatedLattice where

open import Level
open import Algebra
open import Data.Product
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.Lattice using (Supremum; Infimum)

open import WLPretty

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
    isBoundedLattice     : IsBoundedLattice _≈_ _∧_ ⊤ 
    isCommutativeMonoid  : IsCommutativeMonoid _≈_ _⊗_ ⊤ 

  -- TODO define ⇒ 

record ResiduatedLattice c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  constructor mkResiduatedLattice
  infix  4 _≈_ _≤_
  infixr 7 _⊗_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_     : Rel Carrier ℓ₂  -- The partial order.
    _⊗_     : Op₂ Carrier     -- The t-norm
    _⇒_     : Op₂ Carrier     -- The residuum
    _∧_     : Op₂ Carrier     -- The minimum operation.
    _∨_     : Op₂ Carrier     -- The maximum operation.
    ⊤       : Carrier         -- The maximum.
    ⊥       : Carrier         -- The minimum.
    isResiduatedLattice : IsResiduatedLattice _≈_ _≤_ _⊗_ _⇒_ _∧_ _∨_ ⊤ ⊥ 
    doc : Carrier → Doc
    
  open IsResiduatedLattice isResiduatedLattice public

open ResiduatedLattice public
