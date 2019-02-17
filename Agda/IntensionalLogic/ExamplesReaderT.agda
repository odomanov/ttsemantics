
module ExamplesReaderT where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_)

open import Monad.Maybe
open import Monad.Reader   

data World : Set where
  w1 w2 : World

IntMonad = MonadReaderT {World} {{MonadMaybe}}

-- intensional
∧ : ∀ {a} → Set a → Set a
∧ = ReaderT World Maybe 

-- extensional
∨ : ∀ {a} {A : Set a} → ∧ A → World → Maybe A
∨ = runReaderT                  

-- extension in the world w
∨_/_ : ∀ {a} {A : Set a} → ∧ A → World → Maybe A
∨ ma / w = ∨ ma w  

rigid = return

infixl 5 _⋆_

-- simple lifting
_⋆_ : ∀ {i k} {A : Set i} {B : Set k} → ∧ A → (A → B) → ∧ B
ma ⋆ f = liftM f ma 


data Human : Set where
  John Mary Bill : Human

----------------------------------------------------
-- Example: intension for the tallest human

itH : ∧ Human
itH = mkReaderT f 
  where
  f : World → Maybe Human
  f w1 = just John
  f w2 = just Mary

_ : ∨ itH w1 ≡ just John
_ = refl

_ : ∨ itH w2 ≡ just Mary
_ = refl

_ : ∨ itH ≡ λ w → ∨ itH w
_ = refl


-- -- iRun' is itself intensional
-- -- h Run/ w = h runs in the world w

postulate
  _Run : Human → Set
  Jr : John Run  -- proof of "John runs"
  Mr : Mary Run
  Br : Bill Run

_Run/_ : Human → World → Maybe Set
h Run/ w = return (h Run)
  
iRun' : Human → (∧ Set)
iRun' h = mkReaderT (λ w → return (h Run))

_ : ∨ (itH >>= iRun') / w1 ≡ just (John Run) 
_ = refl

_ : ∨ (itH >>= iRun') / w2 ≡ just (Mary Run)
_ = refl

_ : ∨ (rigid John >>= iRun') / w1 ≡ just (John Run) 
_ = refl

_ : ∨ (rigid John >>= iRun') / w2 ≡ just (John Run)
_ = refl




-- composition of calculations -------------------------------------------------
-- (using Maybe and Monad transformer)

iFather : Human → (∧ Human)
iFather h = mkReaderT (Father h)
  where
  Father : Human → World → Maybe Human
  Father John w1 = just Bill
  Father Mary w1 = just Bill
  Father Bill w1 = nothing
  Father John w2 = just Bill
  Father Mary w2 = just John
  Father Bill w2 = nothing


-- the father of the tallest human runs
_ : ∨ (itH >>= iFather >>= iRun') / w1 ≡ (Bill Run/ w1)
_ = refl

_ : ∨ (itH >>= iFather >>= iRun') / w1 ≡ just (Bill Run)
_ = refl

_ : ∨ (itH >>= iFather >>= iRun') / w2 ≡ (John Run/ w2)
_ = refl

_ : ∨ (itH >>= iFather >>= iRun') / w2 ≡ just (John Run)
_ = refl



Father : Human → Maybe Human
Father John = just Bill
Father Mary = just Bill
Father Bill = nothing

-- the father of the tallest human runs
-- _ : ∨ (itH ⋆ Father ⋆ Run) / w1 ≡ (Run Bill)
-- _ = refl

-- _ : ∨ (itH ⋆ Father ⋆ Run) / w1
-- _ = Br





-- singleton "John"
-- ⊤ is the intension (=meaning) of singleton
-- or unique object
sJ : ⊤ → Human
sJ tt = John

isJ : ⊤ → ∧ Human
isJ tt = rigid John

_ : ∨ (rigid tt >>= isJ) / w1 ≡ just John
_ = refl

_ : ∨ (liftM sJ (rigid tt)) / w1 ≡ just John
_ = refl

_ : ∨ ((rigid tt) ⋆ sJ) / w1 ≡ return John
_ = refl

_ : ∨ (rigid tt >>= isJ >>= iRun') / w1 ≡ John Run/ w1
_ = refl

_ : ∨ (rigid tt >>= (λ x → rigid John) >>= iRun') / w1 ≡ John Run/ w1
_ = refl

_ : ∨ (rigid tt >>= isJ >>= iRun') / w1 ≡ just (John Run)
_ = refl

_ : ∨ (rigid tt >>= (λ x → rigid John) >>= iRun') / w1 ≡ just (John Run)
_ = refl



itH' : ⊤ → ∧ Human
itH' tt = mkReaderT f
  where
  f : World → Maybe Human
  f w1 = just John
  f w2 = just Mary

_ : ∨ (rigid tt >>= itH') / w1 ≡ just John
_ = refl

_ : ∨ (rigid tt >>= itH') / w2 ≡ just Mary
_ = refl

_ : ∨ (rigid tt >>= itH') / w1 ≡ return (sJ tt) 
_ = refl





