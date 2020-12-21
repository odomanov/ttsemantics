-- A Writer monad actually, generalized


open import ResiduatedLattice

module FuzzyMonad {c ℓ₁ ℓ₂} (la : ResiduatedLattice c ℓ₁ ℓ₂) where

open import Data.Maybe hiding (_>>=_)
open import Level
open import Algebra renaming (CommutativeMonoid to CM)
open import Data.Product hiding (_<*>_)
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Function using (id; _∘_; const)


import RLMaybe; open RLMaybe la public

record Monad (M : ∀ {a} → Set a → Set (suc (a ⊔ c ⊔ ℓ₁ ⊔ ℓ₂)))
             (fa : ∀ {l} {A : Set l} → M A → A)
             : Setω  where
  constructor mkMonad

  infixl 5 _>>=_ 
  infixl 5 _>>_
  infixl 40 _<$>_ _<*>_

  field
    _>>=_ : ∀ {a b} {A : Set a} {B : A → Set b}
          → (ma : M A)
          → ((x : A) → M (B x))
          → M (B (fa ma))
    return : ∀ {a} {A : Set a} → A → M A

  -- TODO check these definitions; they could be incorrect
  
  _>>_ : ∀ {a b} {A : Set a} {B : A → Set b}
       → (ma : M A)
       → M (B (fa ma))
       → M (B (fa ma))
  m₁ >> m₂ = m₁ >>= const m₂
  
  _=<<_ : ∀ {a b} {A : Set a} {B : A → Set b}
        → ((x : A) → M (B x))
        → (ma : M A)
        → M (B (fa ma))
  mf =<< ma = ma >>= mf

  _<*>_ : ∀ {a b} {A : Set a} {B : A → Set b}
        → M ((x : A) → B x)
        → (ma : M A)
        → M (B (fa ma))
  mf <*> mx = mf >>= λ f → mx >>= λ x → return (f x)

  -- fmap
  _<$>_ : ∀ {a b} {A : Set a} {B : A → Set b}
        → ((x : A) → B x)
        → (ma : M A)
        → M (B (fa ma))
  f <$> m = return f <*> m

  join : ∀ {a} {A : Set a} → M (M A) → M A
  join mma = mma >>= id

  liftM : ∀ {a b} {A : Set a} {B : A → Set b}
        → ((x : A) → B x)
        → (ma : M A)
        → M (B (fa ma))
  liftM f ma = f <$> ma

  liftM2 : ∀ {i j k} {A : Set i} {B : A → Set j} {C : (x : A) → B x → Set k}
         → ((x : A) → (y : B x) → C x y)
         → (ma : M A)
         → (mb : M (B (fa ma)))
         → M (C (fa ma) (fa mb))
  liftM2 f ma mb = f <$> ma <*> mb 



-- Check that MC is a Residuated lattice
_ : IsResiduatedLattice _ _ _ _ _ _ _ _
_ = MCisResiduatedLattice  




-- Fuzzy Type

record Fuzzy {a} (A : Set a) : Set (suc (a ⊔ c ⊔ ℓ₁ ⊔ ℓ₂)) where
  constructor mkFuzzy
  field
    runFuzzy : A × MC
  fa = proj₁ runFuzzy
  fα = proj₂ runFuzzy

open Fuzzy public

private
  retFuzzy : ∀ {a} {A : Set a} → A → Fuzzy A
  runFuzzy (retFuzzy a) = a , MC⊤
  bindFuzzy : ∀ {a b} {A : Set a} {B : A → Set b}
    → (ma : Fuzzy A) → ((y : A) → Fuzzy (B y)) → Fuzzy (B (fa ma))
  runFuzzy (bindFuzzy ma f) = fa mb , fα ma ⟪⨂⟫ fα mb
    where mb = f (fa ma)

MonadFuzzy : Monad Fuzzy fa
MonadFuzzy = record { _>>=_ = bindFuzzy ; return = retFuzzy } 


-- Let's check the Monad Laws 
 
-- unitl : ∀ {i k} {A : Set i} {B : Set k} (a : A) (f : A → Fuzzy B)
--   → (bindFuzzy (retFuzzy a) f) ≡ f a
--   -- → ((return a) >>= f) ≡ f a
-- unitl {i} {k} {A} {B} a f = {!!}
 
-- unitr : ∀ {i} {A : Set i} {ma : Fuzzy S M A}
--   → (bindFuzzy ma retFuzzy) ≡ ma
-- --   → (ma >>= return) ≡ ma
-- unitr = {!refl!}
 
-- assoc : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} →
--   {ma : Fuzzy A} {f : A → Fuzzy B} {g : B → Fuzzy C} → 
--   (bindFuzzy (bindFuzzy ma f) g) ≡ (bindFuzzy ma (λ a → bindFuzzy (f a) g))
--   -- ((ma >>= f) >>= g) ≡ (ma >>= (λ a → f a >>= g))
-- assoc = {!!}
  
