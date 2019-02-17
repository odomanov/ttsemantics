module ExamplesReader where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_)

open import Monad.Identity
open import Monad.Reader   

data World : Set where
  w1 w2 : World
  
IntMonad = MonadReader World

-- intensional
∧ : ∀ {a} → Set a → Set a
∧ = Reader World 

-- extensional
∨ : ∀ {a} {A : Set a} → ∧ A → World → A
∨ = runReader                 

-- extension in the world w
∨_/_ : ∀ {a} {A : Set a} → ∧ A → World → A
∨ ma / w = ∨ ma w  

rigid = return 

infixl 5 _⋆_

-- simple lifting
_⋆_ : ∀ {i k} {A : Set i} {B : Set k} → ∧ A → (A → B) → ∧ B
ma ⋆ f = liftM f ma 


data Human : Set where
  John Mary Bill Unknown : Human


-- Example: rigid designator

iJ : ∧ Human
iJ = rigid John

_ : ∨ iJ / w1 ≡ John
_ = refl

_ : ∨ iJ / w2 ≡ John
_ = refl

_ : ∨ iJ ≡ λ _ → John
_ = refl


----------------------------------------------------
-- Example: intension for the tallest human

-- wrap a function from World into the intensional type
mkIntensional : ∀ {a} {A : Set a} → (World → A) → ∧ A
mkIntensional f = mkReaderT (λ w → mkIdentity (f w))

itH : ∧ Human
itH = mkIntensional f
  where
  f : World → Human
  f w1 = John
  f w2 = Mary

_ : ∨ itH w1 ≡ John
_ = refl

_ : ∨ itH w2 ≡ Mary
_ = refl

_ : ∨ itH ≡ λ w → ∨ itH w
_ = refl



-----------------------------------------------------
-- Example: dependent types


-- one place predicate
-- "Run" is not intensional but can be applied to intensions

postulate
  Run : Human → Set    
  Jr : Run John   -- a proof that John runs
  Br : Run Bill
  Mr⊥ : Run Mary → ⊥
  
-- applying Run to itH (via lifting)

_ : ∨ (liftM Run itH) / w2 ≡ Run Mary
_ = refl

_ : ∨ (liftM Run itH) / w1
_ = Jr

_ : ∨ (itH ⋆ Run) / w2 ≡ Run Mary
_ = refl

_ : ∨ (itH ⋆ Run) / w1
_ = Jr


-- applying via >>=

iRun : Human → (∧ Set) 
iRun = rigid ∘ Run   -- this is liftM actually

_ : ∨ (itH >>= iRun) / w1 ≡ Run John
_ = refl

_ : ∨ (itH >>= iRun) / w1 
_ = Jr

_ : ∨ (itH >>= iRun) / w2 ≡ Run Mary
_ = refl

_ : ∨ (itH >>= iRun) / w2 → ⊥
_ = Mr⊥

_ : ∨ (itH >>= iRun) / w1 ≡ Run John
_ = refl

_ : ∨ (itH >>= iRun) / w1 
_ = Jr

_ : ∨ (itH >>= iRun) / w2 ≡ Run Mary
_ = refl

_ : ∨ (itH >>= iRun) / w2 → ⊥
_ = Mr⊥



-- now "iRun'" is itself intensional
-- h Run/ w = h runs in the world w

postulate
  _Run/_ : Human → World → Set
  Jr1 : John Run/ w1
  Mr2 : Mary Run/ w2
  Jr2⊥ : John Run/ w2 → ⊥
  Br1 : Bill Run/ w1

iRun' : Human → (∧ Set)
iRun' h = mkIntensional (λ w → h Run/ w) 

_ : ∨ (itH >>= iRun') ≡ λ w → (∨ itH w) Run/ w
_ = refl

_ : ∨ (itH >>= iRun') / w1 ≡ John Run/ w1
_ = refl

_ : ∨ (itH >>= iRun') / w1 
_ = Jr1

_ : ∨ (itH >>= iRun') / w2 
_ = Mr2

_ : ∨ (rigid John >>= iRun') / w2 → ⊥ 
_ = Jr2⊥ 



-- two place predicate  -------------------------------------------------

-- "Loves" is intensional
-- h1 Loves h2 / w  =  h1 loves h2 in the world w

postulate
  _Loves_/_ : Human -> Human -> World -> Set
  MlB2 : Mary Loves Bill / w2                     -- Mary loves Bill in w2
  lself1 : ∀ (h : Human) → h Loves h / w1 → ⊥     -- no one loves oneself in w1 
  lself2 : ∀ (h : Human) → h Loves h / w2         -- everyone loves oneself in w2    
  
iLoves : Human → (∧ (Human → Set))
iLoves h = mkIntensional (λ w → (λ h2 → h Loves h2 / w))

_ : ∨ (itH >>= iLoves) / w1 ≡ λ h → (John Loves h / w1)
_ = refl

_ : (∨ (itH >>= iLoves) / w1) Mary ≡ John Loves Mary / w1
_ = refl

_ : (∨ (itH >>= iLoves) / w1) John ≡ John Loves John / w1
_ = refl

_ : (∨ (itH >>= iLoves) / w1) John → ⊥  
_ = λ z → lself1 John z

_ : (∨ (itH >>= iLoves) / w2) Mary ≡ Mary Loves Mary / w2
_ = refl

_ : (∨ (itH >>= iLoves) / w2) Mary   
_ = lself2 Mary

_ : (∨ (itH >>= iLoves) / w2) Bill ≡ Mary Loves Bill / w2
_ = refl

_ : (∨ (itH >>= iLoves) / w2) Bill
_ = MlB2






-- composition of calculations -------------------------------------------------
-- (adding Maybe requires a Monad transformer)

iFather : Human → (∧ Human)
iFather h = mkIntensional (λ w → (Father h w))
  where
  Father : Human → World → Human
  Father John w1 = Bill
  Father Mary w1 = Bill
  Father Bill w1 = Unknown
  Father Unknown w1 = Unknown
  Father John w2 = Bill
  Father Mary w2 = John
  Father Bill w2 = Unknown
  Father Unknown w2 = Unknown


-- the father of the tallest human runs
_ : ∨ (itH >>= iFather >>= iRun') / w1 ≡ (Bill Run/ w1)
_ = refl

_ : ∨ (itH >>= iFather >>= iRun') / w1
_ = Br1

_ : ∨ (itH >>= iFather >>= iRun') / w2 ≡ (John Run/ w2)
_ = refl


-- lifting

Father : Human → Human
Father John = Bill
Father Mary = Bill
Father Bill = Unknown
Father Unknown = Unknown

-- the father of the tallest human runs
_ : ∨ (itH ⋆ Father ⋆ Run) / w1 ≡ (Run Bill)
_ = refl

_ : ∨ (itH ⋆ Father ⋆ Run) / w1
_ = Br





-- singleton "John"
-- ⊤ is the intension (=meaning) of singleton
-- or unique object
sJ : ⊤ → Human
sJ tt = John

isJ : ⊤ → ∧ Human
isJ tt = rigid John

_ : ∨ (rigid tt >>= isJ) / w1 ≡ John
_ = refl

_ : ∨ (liftM sJ (rigid tt)) / w1 ≡ John
_ = refl

_ : ∨ ((rigid tt) ⋆ sJ) / w1 ≡ John
_ = refl

_ : ∨ (rigid tt >>= isJ >>= iRun') / w1 ≡ John Run/ w1
_ = refl

_ : ∨ (rigid tt >>= (λ x → rigid John) >>= iRun') / w1 ≡ John Run/ w1
_ = refl

_ : ∨ (rigid tt >>= (λ x → rigid John) >>= iRun') / w1 
_ = Jr1

_ : ∨ (rigid tt >>= (λ x → rigid John) >>= iRun') / w2 → ⊥
_ = Jr2⊥




-- the tallest human

itH' : ⊤ → ∧ Human
itH' tt = mkIntensional f
  where
  f : World → Human
  f w1 = John
  f w2 = Mary


_ : ∨ (rigid tt >>= itH') / w1 ≡ John
_ = refl

_ : ∨ (rigid tt >>= itH') / w2 ≡ Mary
_ = refl

_ : ∨ (rigid tt >>= itH') / w1 ≡ sJ tt 
_ = refl





