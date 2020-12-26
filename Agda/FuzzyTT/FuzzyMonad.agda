-- A monad for working with Fuzzy types.
-- A Writer monad actually, generalized.


import PersuasionAlgebra 

module FuzzyMonad {c ℓ₁ ℓ₂} (pa : PersuasionAlgebra.PersuasionAlgebra c ℓ₁ ℓ₂) where

open import Level
open import Algebra renaming (CommutativeMonoid to CM)
open import Data.Maybe hiding (_>>=_)
open import Data.Product hiding (_<*>_)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≡-to-≅; ≅-to-≡)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Function using (id; _∘_; const)


import PAMaybe    -- This checks that MC is a Persuasion algebra (if pa is)
open PAMaybe {{pa}} public   

open module PA = PersuasionAlgebra.PersuasionAlgebra pa


-- DependentMonad requires an 'extract' function MA → A, which cannot be defined
-- for any M generally. That's why it is a parameter.
record DependentMonad (M : ∀ {a} → Set a → Set (suc (a ⊔ c ⊔ ℓ₁ ⊔ ℓ₂)))
             (extract : ∀ {l} {A : Set l} → M A → A)
             : Setω  where

  infixl 5 _>>=_ 
  infixl 5 _>>_
  infixl 40 _<$>_ _<*>_

  field
    _>>=_ : ∀ {a b} {A : Set a} {B : A → Set b}
          → (ma : M A)
          → ((x : A) → M (B x))
          → M (B (extract ma))
    return : ∀ {a} {A : Set a} → A → M A

  _>>_ : ∀ {a b} {A : Set a} {B : A → Set b}
       → (ma : M A)
       → M (B (extract ma))
       → M (B (extract ma))
  ma >> mb = ma >>= const mb
  
  _=<<_ : ∀ {a b} {A : Set a} {B : A → Set b}
        → ((x : A) → M (B x))
        → (ma : M A)
        → M (B (extract ma))
  mf =<< ma = ma >>= mf

  _<*>_ : ∀ {a b} {A : Set a} {B : A → Set b}
        → M ((x : A) → B x)
        → (ma : M A)
        → M (B (extract ma))
  mf <*> ma = mf >>= λ f → ma >>= λ x → return (f x)

  -- fmap
  _<$>_ : ∀ {a b} {A : Set a} {B : A → Set b}
        → ((x : A) → B x)
        → (ma : M A)
        → M (B (extract ma))
  f <$> m = return f <*> m

  join : ∀ {a} {A : Set a} → M (M A) → M A
  join mma = mma >>= id

  liftM : ∀ {a b} {A : Set a} {B : A → Set b}
        → ((x : A) → B x)
        → (ma : M A)
        → M (B (extract ma))
  liftM f ma = f <$> ma

  liftM2 : ∀ {i j k} {A : Set i} {B : A → Set j} {C : (x : A) → B x → Set k}
         → ((x : A) → (y : B x) → C x y)
         → (ma : M A)
         → (mb : M (B (extract ma)))
         → M (C (extract ma) (extract mb))
  liftM2 f ma mb = f <$> ma <*> mb 





-- Fuzzy Type

record Fuzzy {a} (A : Set a) : Set (suc (a ⊔ c ⊔ ℓ₁ ⊔ ℓ₂)) where
  constructor _!_
  field
    fa : A
    fα : Carrier

open Fuzzy public


-- (Definitial) equality for fuzzy types
data _f≡_ {i} {A : Set i} (u v : Fuzzy A) : Set (suc (i ⊔ c ⊔ ℓ₁ ⊔ ℓ₂)) where
  frefl : fa u ≅ fa v → (fα u) ≈ (fα v) → u f≡ v


-- Defining the monad.

private
  retFuzzy : ∀ {a} {A : Set a} → A → Fuzzy A
  fa (retFuzzy a) = a
  fα (retFuzzy a) = ε
  bindFuzzy : ∀ {a b} {A : Set a} {B : A → Set b}
              → (ma : Fuzzy A)
              → ((y : A) → Fuzzy (B y))
              → Fuzzy (B (fa ma))
  fa (bindFuzzy (a ! α) f) = fa (f a) 
  fα (bindFuzzy (a ! α) f) = α ⊗ fα (f a)

MonadFuzzy : DependentMonad Fuzzy fa
MonadFuzzy = record { _>>=_ = bindFuzzy ; return = retFuzzy } 

open DependentMonad MonadFuzzy


-- Let's check the Monad Laws 

unitl : ∀ {i k} {A : Set i} {B : A → Set k} (a : A) (f : (x : A) → Fuzzy (B x))
  -- → (bindFuzzy (retFuzzy a) f) f≡ (f a)
  → ((return a) >>= f) f≡ (f a)
unitl a f = frefl _≅_.refl (CM.identityˡ CommMon (fα (f a))) 

unitr : ∀ {i} {A : Set i} (ma : Fuzzy A)
  -- → (bindFuzzy ma retFuzzy) f≡ ma
  → (ma >>= return) f≡ ma
unitr ma = frefl _≅_.refl (CM.identityʳ CommMon (fα ma))
 
assoc : ∀ {i j k} {A : Set i} {B : A → Set j} {C : (x : A) → B x → Set k} →
  (ma : Fuzzy A) (f : (x : A) → Fuzzy (B x)) (g : {x : A} (y : B x) → Fuzzy (C x y)) → 
  -- (bindFuzzy (bindFuzzy ma f) g) f≡ (bindFuzzy ma (λ a → bindFuzzy (f a) g))
  ((ma >>= f) >>= g) f≡ (ma >>= (λ a → f a >>= g))
assoc (a ! α) f g = frefl _≅_.refl (CM.assoc CommMon α (fα (f a)) (fα (g (fa (f a)))))
  
