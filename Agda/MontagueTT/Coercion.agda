-- Adapted from: https://github.com/shhaumb/agda_coercion

module Coercion where

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Level renaming (suc to lsuc)

data _<:_ {l m} : (A : Set l) → (B : Set m) → Set (lsuc (l ⊔ m)) where
  coerce : {A : Set l} → {B : Set m} → (A → B) → (A <: B)

getfunc : ∀ {l m} → {A : Set l} → {B : Set m} → (A <: B) → (A → B)
getfunc (coerce f) = f

identityCoercion : ∀ {l} → {A : Set l} → A <: A
identityCoercion {_} {A} = coerce (λ(x : A) → x)

refinementCoercionFunc : (A : Set) → (f : A → Set) → Σ A f → A
refinementCoercionFunc A f (a , _) = a

refinementCoercion : {A : Set} → {f : A → Set} → (Σ A f <: A)
refinementCoercion {A} {f} = coerce (refinementCoercionFunc A f)


⟪_⟫ : ∀ {m n} {A : Set m} {B : Set n} → A → {{_ : A <: B}} → B
⟪ a ⟫ {{c}} = getfunc c a

⟪→_⟫ : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → (B → C) → {{_ : A <: B}} → (A → C)
⟪→ f ⟫ b = f ⟪ b ⟫ 

⟪Σ⟫ : ∀ {i j k} (A : Set i) {B : Set j} (C : B → Set k) → {{_ : A <: B}} → Set (i ⊔ k)
⟪Σ⟫ A C = Σ A ⟪→ C ⟫

_⟪∘⟫_ : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → B <: C → A <: B → A <: C
cbc ⟪∘⟫ cab = coerce (getfunc cbc ∘ getfunc cab)

-- Equality with coercion. Can be used for redefining ≡.
_⟪≡⟫_ : ∀ {a} {A B C : Set a} {{_ : A <: C}} {{_ : B <: C}} (x : A) (y : B) → Set a
_⟪≡⟫_ x y = ⟪ x ⟫ ≡ ⟪ y ⟫

-- Coercion respects equality
≡-coerce : ∀ {a b} {A : Set a} {C : Set b} {x y : A} → x ≡ y → {{_ : A <: C}} → ⟪ x ⟫ ≡ ⟪ y ⟫
≡-coerce refl {{c}} = refl

