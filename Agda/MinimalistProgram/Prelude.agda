-- Prelude to Minimalist Program

module _ where

open import Data.Bool
open import Data.Fin
open import Data.List
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.String hiding (_==_)

record Eq (A B : Set): Set where
  field
    _==_ : A → B → Bool

open Eq {{...}} public

_∈_ : ∀ {A : Set} → {{Eq A A}} → A → List A → Bool
x ∈ [] = false
x ∈ (v ∷ vs) with x == v
... | true  = true
... | false = x ∈ vs
-- x ∈ xs = any (λ v → v == x) xs

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

  EqString : Eq String String
  _==_ {{EqString}} = Data.String._==_



ListPermutations : {A : Set} → (List A) → (List (List A))
ListPermutations [] = [] ∷ []
ListPermutations (x ∷ xs) =
  foldr (λ fl fls → (add x fl) Data.List.++ fls) [] (ListPermutations xs)
  where
  addAcc : {A : Set} → A → List A → List A → List (List A)
  addAcc x acc [] = (acc ∷ʳ x) ∷ []
  addAcc x acc ly@(y ∷ ys) =
    (addAcc x (acc ∷ʳ y) ys) ∷ʳ (acc Data.List.++ (x ∷ ly)) 

  add : {A : Set} → A → List A → List (List A)
  add x xs = addAcc x [] xs

private

  module test1 where

    open import Relation.Binary.PropositionalEquality using (_≡_; refl)

    _ : (A : Set) → ListPermutations {A} [] ≡ [] ∷ []
    _ = λ _ → refl


-- remove the first matching element from the list
remove-first : {A : Set} → List A → A → {{Eq A A}} → List A
remove-first l a = removeAcc l a []
  where
  removeAcc : {A : Set} → List A → A → (acc : List A) → {{Eq A A}} → List A
  removeAcc [] _ acc = acc
  removeAcc (x ∷ xs) a acc with x == a
  ... | true  = acc Data.List.++ xs
  ... | false = removeAcc xs a (acc Data.List.++ (x ∷ []))


private

  module test2 where
  
    open import Relation.Binary.PropositionalEquality using (_≡_; refl)
      
    _ : remove-first [] 4 ≡ []
    _ = refl
    
    _ : remove-first (1 ∷ 4 ∷ []) 4 ≡ (1 ∷ [])
    _ = refl
    
    _ : remove-first (1 ∷ 4 ∷ []) 1 ≡ (4 ∷ [])
    _ = refl
  
    _ : remove-first (1 ∷ 4 ∷ 7 ∷ 9 ∷ []) 1 ≡ (4 ∷ 7 ∷ 9 ∷ [])
    _ = refl
  
    _ : remove-first (1 ∷ 4 ∷ 7 ∷ 9 ∷ []) 9 ≡ (1 ∷ 4 ∷ 7 ∷ [])
    _ = refl
  
    _ : remove-first (1 ∷ 4 ∷ 7 ∷ 9 ∷ []) 7 ≡ (1 ∷ 4 ∷ 9 ∷ [])
    _ = refl
  
    _ : remove-first (1 ∷ 4 ∷ 7 ∷ 9 ∷ []) 888 ≡ (1 ∷ 4 ∷ 7 ∷ 9 ∷ [])
    _ = refl
