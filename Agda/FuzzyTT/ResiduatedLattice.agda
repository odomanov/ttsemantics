module ResiduatedLattice where

open import Algebra
open import Data.Nat using (ℕ)
open import Data.Product
open import Level
open import Relation.Binary
open import Relation.Binary.Lattice using (Supremum; Infimum)
-- open import Relation.Binary.Properties.BoundedLattice --using (Supremum; Infimum)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary

open import WLPretty

record IsResiduatedLattice {c ℓ₁ ℓ₂} {A : Set c}
                         (_≈_ : Rel A ℓ₁)
                         (_≤_ : Rel A ℓ₂)
                         (_⊗_ : Op₂ A)
                         -- (_⊕_ : Op₂ A)
                         -- (_⊖_ : Op₂ A)
                         -- (⊘   : Op₁ A)          -- negation
                         (_∧_ : Op₂ A)
                         (_∨_ : Op₂ A)
                         -- (mean : A → A → ℕ → A) -- <n> → <n+1>
                         -- (adiff : Op₂ A)
                         (⊤ : A)
                         (⊥ : A)
                         : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    -- isPOrder  : IsPartialOrder _≈_ _≤_ 
    -- sup       : Supremum _≤_ _∨_
    -- inf       : Infimum  _≤_ _∧_
    -- maximum   : Maximum _≤_ ⊤
    -- minimum   : Minimum _≤_ ⊥
    -- isLattice : IsLattice _≤_ _∨_ _∧_
    isBoundedLattice     : IsBoundedLattice _≈_ _∧_ ⊤ 
    isCommutativeMonoid  : IsCommutativeMonoid _≈_ _⊗_ ⊤ 
    -- support
    -- ⊗-comm    : Commutative _≈_ _⊗_
    -- ⊗-mono    : ∀ p q r → p ≤ q → (p ⊗ r) ≤ (q ⊗ r) --  Monotone 
    -- ⊗-assoc   : Associative _≈_ _⊗_
    -- ⊗-neut    : ∀ a → (a ⊗ ⊤) ≈ a
    -- aggregation    
    -- ⊕-comm    : Commutative _≈_ _⊕_
    -- ⊕-mono    : ∀ p q r → p ≤ q → (p ⊕ r) ≤ (q ⊕ r) --  Monotone 
    -- ⊕-assoc   : Associative _≈_ _⊕_
    -- ⊕-neut    : ∀ a → (a ⊕ ⊥) ≈ a
    -- conflict
    -- ⊖-1       : ∀ (a b) → b ≤ a → ¬ a ≈ b → (a ⊖ b) ≤ a
    -- ⊖-2       : ∀ (a b) → a ≤ b → (a ⊖ b) ≈ ⊥
    -- ⊖-mono    : ∀ (p q r) → p ≤ q → (p ⊖ r) ≤ (q ⊖ r) --  Monotone 
    -- ⊖-neut    : ∀ (a) → (a ⊖ ⊥) ≈ a
    -- ⊖-3       : ∀ (a b) → (a ⊖ b) ≈ ⊥ → (b ⊖ a) ≈ ⊥ → a ≈ b
    -- ⊖-4       : ∀ (a b) → (a ⊕ b) ≤ ⊤ → ¬ ((a ⊕ b) ≈ ⊤) → ((a ⊕ b) ⊖ b) ≈ a

  -- meanv : ∀ {n} → Mean A (ℕ.suc n) → A
  -- meanv {ℕ.zero}  (mn1 a) = a
  -- meanv {ℕ.suc n} (mn+ a acc) = mean a (meanv acc) n



record ResiduatedLattice c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  constructor mkResiduatedLattice
  infix  4 _≈_ _≤_
  -- infixr 6 _⊕_
  -- infixr 7 _⊖_
  infixr 7 _⊗_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_     : Rel Carrier ℓ₂  -- The partial order.
    _⊗_     : Op₂ Carrier     -- The support operation.
    -- _⊕_     : Op₂ Carrier     -- The aggregation operation.
    -- _⊖_     : Op₂ Carrier     -- The conflict operation.
    -- ⊘       : Op₁ Carrier     -- The negation operation.
    _∧_     : Op₂ Carrier     -- The minimum operation.
    _∨_     : Op₂ Carrier     -- The maximum operation.
    ⊤       : Carrier         -- The maximum.
    ⊥       : Carrier         -- The minimum.
    isResiduatedLattice : IsResiduatedLattice _≈_ _≤_ _⊗_ _∧_ _∨_ ⊤ ⊥ 
    doc : Carrier → Doc
    
  open IsResiduatedLattice isResiduatedLattice public

open ResiduatedLattice public
