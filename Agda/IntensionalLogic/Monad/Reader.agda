
module Monad.Reader where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Function using (id; _∘_)

open import Monad.Identity
open import Monad public

record ReaderT {a} (R : Set) (M : ∀ {ℓ} → Set ℓ → Set ℓ) (A : Set a) : Set a where
  constructor mkReaderT
  field
    runReaderT : R → M A

open ReaderT public

module _ {R : Set} {M : ∀ {ℓ} → Set ℓ → Set ℓ} {{_ : Monad M}} where

  private
    retReaderT : ∀ {a} {A : Set a} → A → ReaderT R M A
    runReaderT (retReaderT a) r = return a
    bindReaderT : ∀ {a b} {A : Set a} {B : Set b}
      → ReaderT R M A → (A → ReaderT R M B) → ReaderT R M B
    runReaderT (bindReaderT ma f) r = runReaderT ma r >>= λ x → runReaderT (f x) r
  
  instance
    MonadReaderT : Monad (ReaderT R M)  
    return {{MonadReaderT}} = retReaderT
    _>>=_ {{MonadReaderT}} = bindReaderT
    
  asks : ∀ {a} {A : Set a} → (R → A) → ReaderT R M A
  runReaderT (asks f) r = return (f r) 
  
  ask : ReaderT R M R
  ask = asks id
  
  local : ∀ {a} {A : Set a} → (R → R) → ReaderT R M A → ReaderT R M A
  runReaderT (local f m) r = runReaderT m (f r)
  
    
  -- Let's check the Monad Laws 
   
  -- unitl : ∀ {i k} {A : Set i} {B : Set k} {a : A} {f : A → ReaderT R M B}
  --   → (bindReaderT (retReaderT a) f) ≡ f a
  --   -- → ((return a) >>= f) ≡ f a
  -- unitl = {!refl!} 
   
  -- unitr : ∀ {i} {A : Set i} {ma : ReaderT R M A}
  --   → (bindReaderT ma retReaderT) ≡ ma
  -- --   → (ma >>= return) ≡ ma
  -- unitr = {!refl!}
   
  -- assoc : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} →
  --   {ma : ReaderT R M A} {f : A → ReaderT R M B} {g : B → ReaderT R M C} → 
  --   (bindReaderT (bindReaderT ma f) g) ≡ (bindReaderT ma (λ a → bindReaderT (f a) g))
  --   -- ((ma >>= f) >>= g) ≡ (ma >>= (λ a → f a >>= g))
  -- assoc = {!refl!}
    

Reader : ∀ {a} (R : Set) (A : Set a) → Set a
Reader R = ReaderT R Identity

runReader : ∀ {a} {R : Set} {A : Set a} → Reader R A → R → A
runReader m r = runIdentity (runReaderT m r)

MonadReader : ∀ (R : Set) → Monad (Reader R)
MonadReader R = MonadReaderT {{MonadId}}  

