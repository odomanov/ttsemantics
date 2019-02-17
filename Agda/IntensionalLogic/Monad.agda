module Monad where

open import Agda.Primitive
open import Function using (id; _∘_)

record Monad (M : ∀ {ℓ} → Set ℓ → Set ℓ) : Setω  where
  constructor mkMonad

  infixl 5 _>>=_ _>>_
  infixl 40 _<$>_ _<*>_

  field
    _>>=_ : ∀ {a b} {A : Set a} {B : Set b} -> M A -> (A -> M B) -> M B
    return : ∀ {a} {A : Set a} -> A -> M A

  -- TODO check these definitions; they could be incorrect
  
  _>>_ : ∀ {a b} {A : Set a} {B : Set b} -> M A -> M B -> M B
  m₁ >> m₂ = m₁ >>= \_ -> m₂
  
  _<*>_ : ∀ {a b} {A : Set a} {B : Set b} -> M (A -> B) -> M A -> M B
  mf <*> mx = mf >>= \f -> mx >>= \x -> return (f x)

  -- fmap
  _<$>_ : ∀ {a b} {A : Set a} {B : Set b} -> (A -> B) -> M A -> M B
  f <$> m = return f <*> m

  join : ∀ {a} {A : Set a} → M (M A) → M A
  join mma = mma >>= id

  liftM : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → M A → M B
  liftM f ma = ma >>= (return ∘ f)

  liftM2 : ∀ {i j k} → {A : Set i} {B : Set j} {C : Set k} →
    (A → B → C) → M A → M B → M C
  liftM2 f ma mb = ma >>= λ x → mb >>= λ y → return (f x y)

open Monad {{...}} public

