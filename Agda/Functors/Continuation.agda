-- Continuation monad -- no transformer
{-# OPTIONS --cumulativity #-}
module _ where

open import Data.Product
open import Data.Unit
open import Function using (_$_; id; flip)
open import Relation.Binary.PropositionalEquality
open import Level 
1ℓ = suc 0ℓ
2ℓ = suc 1ℓ

open import Category.Monad
open import Category.Monad.Indexed
open import Category.Monad.Continuation

K : ∀{a}{b}(R : Set a) → ⊤ → Set (a ⊔ b)
K {a} {b} R tt = R

Cont : ∀{a b}(R : Set a) → Set (a ⊔ b) → Set (a ⊔ b)
Cont {a} {b} R = DCont {f = a ⊔ b} (K R) tt tt  

MonadICont : ∀{a}{b}(R : Set a) → RawIMonad (DCont {f = a ⊔ b} (K R)) 
MonadICont {a} {b} R = DContIMonad {f = a ⊔ b} (K R)

-- проверим монадные законы
module Laws {a} {b} {R : Set a} where

  open RawIMonad (MonadICont {a} {b} R)
  
  unitl : ∀{A B : Set b}{x : A}{f : A → Cont {a} {b} R B}
    → (return x >>= f) ≡ f x
  unitl = refl

  unitr : ∀{A : Set b}{ma : Cont {a} {b} R A}
    → (ma >>= return) ≡ ma
  unitr = refl

  assoc : ∀{A B C : Set b} 
    → {ma : Cont {a} {b} R A} {f : A → Cont {a} {b} R B} {g : B → Cont {a} {b} R C}  
    → ((ma >>= f) >>= g) ≡ (ma >>= (λ a → f a >>= g))
  assoc = refl
    
open RawIMonad (MonadICont Set) 

postulate
  Human   : Set
  John    : Human
  _runs   : Human → Set
  _loves_ : Human → Human → Set

some : (A : Set) → Cont Set A
some A k = Σ[ x ∈ A ] k x

every : (A : Set) → Cont Set A
every A k = ∀(x : A) → k x

someone  = some  Human
everyone = every Human

app1 : (Human → Set) → Human → Cont Set Set 
app1 v x = return (v x)

_*runs : Human → Cont Set Set
x *runs = return (x runs)     

John-runs : Cont Set Set
John-runs = John *runs

_ : John-runs id ≡ (John runs)
_ = refl

*John : Cont Set Human
*John = return John

John-runs' : Cont Set Set
John-runs' = *John >>= _*runs

_ : John-runs' id ≡ (John runs)
_ = refl

someone-runs : Cont Set Set
someone-runs = someone >>= _*runs    

_ : someone-runs id ≡ (Σ[ x ∈ Human ] x runs)
_ = refl

someone-runs₁ : Cont Set Set
someone-runs₁ = someone >>= (λ x → x *runs)

_ : someone-runs₁ id ≡ (Σ[ x ∈ Human ] x runs)
_ = refl

someone-runs₂ : Cont Set Set
someone-runs₂ = do
  x ← someone
  x *runs 

_ : someone-runs₂ id ≡ (Σ[ x ∈ Human ] x runs)
_ = refl

everyone-runs : Cont Set Set
everyone-runs = do
  x ← everyone
  x *runs

_ : everyone-runs id ≡ (∀(x : Human) → x runs)
_ = refl


-- транзитивные глаголы

_*loves_ : Human → Human → Cont Set Set
_*loves_ x y = return (x loves y)

John-loves-someone₁ : Cont Set Set
John-loves-someone₁ = *John >>= λ y → someone >>= _*loves y 

John-loves-someone₃ : Cont Set Set
John-loves-someone₃ = do
  x ← *John
  y ← someone
  x *loves y

_ : John-loves-someone₃ id ≡ (Σ[ x ∈ Human ] John loves x)
_ = refl


-- зависимость от порядка
-- ======================

-- de dicto

everyone-loves-someone : Cont Set Set
everyone-loves-someone = everyone >>= (λ x →
                                      someone >>= (λ y →
                                                  return (x loves y)))

everyone-loves-someone' : Cont Set Set
everyone-loves-someone' = do
  x  ← everyone
  y  ← someone 
  return (x loves y)

everyone-loves-someone₁ : Cont Set Set
everyone-loves-someone₁ = do
  x  ← everyone
  y  ← someone 
  return (x loves y)

_ : everyone-loves-someone₁ id ≡ ((x : Human) → Σ[ y ∈ Human ] x loves y)
_ = refl


-- de re

everyone-loves-someone₂ : Cont Set Set
everyone-loves-someone₂ = do
  x ← someone 
  y ← everyone
  return (y loves x)

_ : everyone-loves-someone₂ id ≡ (Σ[ x ∈ Human ] (∀(y : Human) → y loves x))
_ = refl


-- belief
-- ======

postulate
  Ralph      : Human
  _is-spy    : Human → Set
  _believes_ : Human → Set → Set

-- Ralph believes someone is a spy
Ralph-believes-some-spy₁ : Cont Set Set
Ralph-believes-some-spy₁ = do
  x ← someone
  return (Ralph believes (x is-spy))

_ : Ralph-believes-some-spy₁ id ≡ (Σ[ x ∈ Human ] Ralph believes (x is-spy))
_ = refl

_*is-spy : Human → Cont Set Set
x *is-spy = return (x is-spy)

some-spy : Cont Set Set
some-spy = someone >>= _*is-spy  
_ : some-spy id ≡ Σ Human _is-spy
_ = refl


-- Ральф верит об s1, что P s1
record RB {a} (A : Set a) (P : A → Set) : Set a where
  field
    s1 : A
    s2 : P s1

infix 2 RB
syntax RB A (λ x → P) = RB[ x ∈ A ] P 

RBel : Cont Set Human
RBel = λ k → RB[ x ∈ Human ] k x

RBel-some-spy₁ : Cont Set Set
RBel-some-spy₁ = do
  x ← RBel
  x *is-spy
  
_ : RBel-some-spy₁ id ≡ (RB Human (λ x → x is-spy))
_ = refl
  
_ : RBel-some-spy₁ id ≡ (RB[ x ∈ Human ] x is-spy)
_ = refl
  
RBel-some-spy₂ : Cont Set Set
RBel-some-spy₂ = do
  x ← someone
  RBel
  x *is-spy

_ : RBel-some-spy₂ id ≡ (Σ[ x ∈ Human ] RB Human (λ _ → x is-spy))
_ = refl
  
_ : RBel-some-spy₂ id ≡ (Σ[ x ∈ Human ] RB[ _ ∈ Human ] x is-spy)
_ = refl

-- Ральф верит, что все шпионы
RBel-all-spies : Cont Set Set
RBel-all-spies = do
  RBel 
  x ← everyone
  x *is-spy

_ : RBel-all-spies id ≡ (RB[ _ ∈ Human ] (∀(x : Human) → x is-spy))
_ = refl

-- Ральф верит, что P
RBelp : ∀{a}{A : Set a}(P : Set) → Set a
RBelp {a}{A} P = RB A (λ _ → P)

_ : RBel-some-spy₂ id ≡ (Σ[ x ∈ Human ] RBelp (x is-spy))
_ = refl

_ : RBel-all-spies id ≡ (RBelp (∀(x : Human) → x is-spy))
_ = refl

