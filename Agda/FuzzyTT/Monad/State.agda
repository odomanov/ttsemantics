
module Monad.State where

open import Level
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Function using (id; _∘_)

open import Monad.Identity
open import Monad public

record StateT {a} (S : Set) (M : ∀ {ℓ} → Set ℓ → Set ℓ) (A : Set a) : Set a where
  constructor mkStateT
  field
    runStateT : S → M (A × S)

open StateT public

module _ {S : Set} {M : ∀ {ℓ} → Set ℓ → Set ℓ} {{_ : Monad M}} where

  private
    retStateT : ∀ {a} {A : Set a} → A → StateT S M A
    runStateT (retStateT a) s = return (a , s)
    bindStateT : ∀ {a b} {A : Set a} {B : Set b}
      → StateT S M A → (A → StateT S M B) → StateT S M B
    runStateT (bindStateT ma f) s = runStateT ma s >>= λ (a , s') → runStateT (f a) s' 
  
  instance
    MonadStateT : Monad (StateT S M)  
    return {{MonadStateT}} = retStateT
    _>>=_ {{MonadStateT}} = bindStateT

  put : ∀ {a} {A : Set a} → S → StateT S M ⊤
  put s = return tt

  get : ∀ {a} {A : Set a} → S → StateT S M S
  get s = return s

 
  -- Let's check the Monad Laws 
   
  unitl : ∀ {i k} {A : Set i} {B : Set k} (a : A) (f : A → StateT S M B)
    → (bindStateT (retStateT a) f) ≡ f a
    -- → ((return a) >>= f) ≡ f a
  unitl {i} {k} {A} {B} a f = {!refl!} 
   
  unitr : ∀ {i} {A : Set i} {ma : StateT S M A}
    → (bindStateT ma retStateT) ≡ ma
  --   → (ma >>= return) ≡ ma
  unitr = {!refl!}
   
  -- assoc : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} →
  --   {ma : StateT S M A} {f : A → StateT S M B} {g : B → StateT S M C} → 
  --   (bindStateT (bindStateT ma f) g) ≡ (bindStateT ma (λ a → bindStateT (f a) g))
  --   -- ((ma >>= f) >>= g) ≡ (ma >>= (λ a → f a >>= g))
  -- assoc = {!refl!}
    

-- Transformer

State : ∀ {a} (S : Set) (A : Set a) → Set a
State S = StateT S Identity

runState : ∀ {a} {S : Set} {A : Set a} → State S A → S → (A × S)
runState m s = runIdentity (runStateT m s)

MonadState : ∀ (S : Set) → Monad (State S)
MonadState S = MonadStateT {{MonadId}}  

