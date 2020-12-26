module _ where

open import Level
open import Algebra
open import Data.Product
open import Relation.Binary hiding (_⇒_)

open import WLPretty hiding (_<$>_)

record IsPersuasionAlgebra {c ℓ₁ ℓ₂} {A : Set c}
                         (_≈_ : Rel A ℓ₁)
                         (_≤_ : Rel A ℓ₂)
                         (_⊗_ : Op₂ A)
                         (ε : A)
                         : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    isPartialOrder       : IsPartialOrder _≈_ _≤_
    isCommutativeMonoid  : IsCommutativeMonoid _≈_ _⊗_ ε 


record PersuasionAlgebra c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  constructor mkPersuasionAlgebra
  infix  4 _≈_ _≤_
  infixr 7 _⊗_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_     : Rel Carrier ℓ₂  -- The partial order.
    _⊗_     : Op₂ Carrier     -- The t-norm
    ε          : Carrier      -- The neutral element.
    isPersuasionAlgebra : IsPersuasionAlgebra _≈_ _≤_ _⊗_ ε
    doc : Carrier → Doc
    
  open IsPersuasionAlgebra isPersuasionAlgebra public

open PersuasionAlgebra {{...}} public
