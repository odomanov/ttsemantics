module _ where

open import Level
open import Algebra
open import Data.Product
open import Relation.Binary hiding (_⇒_)
-- open import Relation.Binary.Lattice using (Supremum; Infimum)

open import WLPretty

record IsPersuasionAlgebra {c ℓ₁ ℓ₂} {A : Set c}
                         (_≈_ : Rel A ℓ₁)
                         (_≤_ : Rel A ℓ₂)
                         (_⊗_ : Op₂ A)
                         -- (_⇒_ : Op₂ A)
                         -- (_∧_ : Op₂ A)
                         -- (_∨_ : Op₂ A)
                         -- (⊤ : A)
                         -- (⊥ : A)
                         (ε : A)
                         : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    isPartialOrder       : IsPartialOrder _≈_ _≤_
    isCommutativeMonoid  : IsCommutativeMonoid _≈_ _⊗_ ε 

  -- TODO define ⇒ ?

record PersuasionAlgebra c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  constructor mkPersuasionAlgebra
  infix  4 _≈_ _≤_
  infixr 7 _⊗_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_     : Rel Carrier ℓ₂  -- The partial order.
    _⊗_     : Op₂ Carrier     -- The t-norm
    -- _⇒_     : Op₂ Carrier     -- The residuum
    -- _∧_     : Op₂ Carrier     -- The minimum operation.
    -- _∨_     : Op₂ Carrier     -- The maximum operation.
    -- ⊤       : Carrier         -- The maximum.
    -- ⊥       : Carrier         -- The minimum.
    ε          : Carrier         -- The neutral.
    isPersuasionAlgebra : IsPersuasionAlgebra _≈_ _≤_ _⊗_ ε
    doc : Carrier → Doc
    
  open IsPersuasionAlgebra isPersuasionAlgebra public

open PersuasionAlgebra public
