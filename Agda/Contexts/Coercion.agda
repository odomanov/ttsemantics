-- Adapted from: https://github.com/shhaumb/agda_coercion

module Coercion where

open import Level
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data _<:_ {l m} : (A : Set l) → (B : Set m) → Set (suc (l ⊔ m)) where
  coerce : {A : Set l} → {B : Set m} → (A → B) → (A <: B)

getfunc : ∀ {l m} → {A : Set l} → {B : Set m} → (A <: B) → (A → B)
getfunc (coerce f) = f

_::_=>_ : ∀ {l m} → Set l  → (n : Level) → Set m → Set ((suc l) ⊔ m ⊔ (suc n))
_::_=>_ x n y = {A : Set n} → (a : A) → {{c : A <: x}} → y

coercive : ∀ {l m n} → {A : Set l} → {B : Set m} → (A → B) → (A :: n => B)
coercive f a {{c}} = f ((getfunc c) a)

-- data _&_ : (A : Set) → (A → Set) → Set1 where
--   #_ : {A : Set} → {f : A → Set} →  (a : A) → {{c : f a}} → (A & f)

identityCoercion : ∀ {l} → {A : Set l} → A <: A
identityCoercion {_} {A} = coerce (λ(x : A) → x)

refinementCoercionFunc : (A : Set) → (f : A → Set) → Σ A f → A
refinementCoercionFunc A f (a , _) = a

refinementCoercion : {A : Set} → {f : A → Set} → (Σ A f <: A)
refinementCoercion {A} {f} = coerce (refinementCoercionFunc A f)


⟪_⟫ : ∀ {m n} {A : Set m} {B : Set n} → A → {{_ : A <: B}} → B
⟪ a ⟫ {{c}} = getfunc c a

-- ⟪_⟫ : ∀ {l m n} {A : Set l} {B : Set m} {C : Set n}
--       → A → {{_ : A <: B}} → {{_ : B <: C}} → C
-- ⟪ a ⟫ {{c1}} {{c2}} = ((getfunc c2) ∘ (getfunc c1)) a

-- Equality with coercion. Can be used for redefining ≡.
_≡c_ : ∀ {a} {A B C : Set a} {{_ : A <: C}} {{_ : B <: C}} (x : A) (y : B) → Set a
_≡c_ x y = ⟪ x ⟫ ≡ ⟪ y ⟫

-- Coercion respects equality
≡-coerce : ∀ {a b} {A : Set a} {C : Set b} {x y : A} → x ≡ y → {{_ : A <: C}} → ⟪ x ⟫ ≡ ⟪ y ⟫
≡-coerce refl {{c}} = refl

