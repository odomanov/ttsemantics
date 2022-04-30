-- Prelude to Minimalist Program

module _ where

open import Data.Bool
open import Data.Fin
open import Data.List
open import Data.Maybe
open import Data.Nat
open import Data.Product

record Eq (A B : Set): Set where
  field
    _==_ : A → B → Bool

open Eq {{...}} public

_∈_ : ∀ {A : Set} → {{Eq A A}} → A → List A → Bool
x ∈ xs = any (λ v → v == x) xs

instance
  Eqℕ : Eq ℕ ℕ
  _==_ {{Eqℕ}} = _≡ᵇ_

  EqFin : ∀ {n m} → Eq (Fin n) (Fin m)
  _==_ ⦃ EqFin {n} {m} ⦄ zero zero = n == m
  _==_ ⦃ EqFin {n} {m} ⦄ (suc i1) (suc i2) = (n == m) ∧ i1 == i2
  _==_ ⦃ EqFin ⦄ _ _ = false

  Eq× : {A B : Set} → {{Eq A A}} → {{Eq B B}} → Eq (A × B) (A × B)
  _==_ {{Eq×}} x y = (proj₁ x == proj₁ y) ∧ (proj₂ x == proj₂ y)

  Eq×× : {A B C : Set} → {{Eq A A}} → {{Eq B B}} → {{Eq C C}} → Eq (A × B × C) (A × B × C)
  _==_ {{Eq××}} x y = (proj₁ x == proj₁ y) ∧ (proj₂ x == proj₂ y)

  EqMaybe : ∀ {A : Set} → {{Eq A A}} → Eq (Maybe A) (Maybe A)
  _==_ ⦃ EqMaybe ⦄ (just x) (just y) = x == y
  _==_ ⦃ EqMaybe ⦄ nothing nothing = true
  _==_ ⦃ EqMaybe ⦄ _ _ = false

