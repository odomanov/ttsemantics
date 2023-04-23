-- Continuation monad -- no transformer
{-# OPTIONS --cumulativity #-}
module _ where

open import Data.Product
open import Function using (_$_; id)
open import Relation.Binary.PropositionalEquality
open import Level 
1ℓ = suc 0ℓ
2ℓ = suc 1ℓ

-- прямое определение, без runCont

open import Category.Monad

Cont : ∀{a b}(R : Set a) → Set (a ⊔ b) → Set (a ⊔ b)
Cont R A = (A → R) → R

MonadCont : ∀{a b} (R : Set a) → RawMonad (Cont {a} {b} R)
-- MonadCont R = record { return = λ a k → k a
--                      ; _>>=_ = λ ma f k → ma (λ x → f x k)
--                      }
RawMonad.return (MonadCont {a} {b} R) x = λ k → k x
RawMonad._>>=_  (MonadCont {a} {b} R) ma f = λ k → ma (λ x → f x k)

-- проверим монадные законы
module Laws {a} {b} {R : Set a} where

  open RawMonad (MonadCont {a} {b} R)
  
  unitl : ∀{A : Set b}{B : Set b}{x : A}{f : A → Cont {a} {b} R B}
    → (return x >>= f) ≡ f x
  unitl = refl

  unitr : ∀{A : Set b}{ma : Cont {a} {b} R A}
    → (ma >>= return) ≡ ma
  unitr = refl

  assoc : ∀ {A : Set b} {B : Set b} {C : Set b} 
    → {ma : Cont {a} {b} R A} {f : A → Cont {a} {b} R B} {g : B → Cont {a} {b} R C}  
    → ((ma >>= f) >>= g) ≡ (ma >>= (λ a → f a >>= g))
  assoc = refl
    
open RawMonad (MonadCont Set) 

postulate
  Human   : Set
  _runs   : Human → Set
  _loves_ : Human → Human → Set
  
some : Cont Set Human
some = λ k → Σ[ x ∈ Human ] k x

every : Cont Set Human
every = λ k → ∀(x : Human) → k x

some-human-runs₁ : Cont Set Set
some-human-runs₁ = some >>= (λ x →
                   return (x runs))

_ : some-human-runs₁ id ≡ (Σ[ x ∈ Human ] x runs)
_ = refl

some-human-runs₂ : Cont Set Set
some-human-runs₂ = do
  x ← some
  return (x runs)

_ : some-human-runs₂ id ≡ (Σ[ x ∈ Human ] x runs)
_ = refl

every-human-runs : Cont Set Set
every-human-runs = do
  x ← every
  return (x runs)

_ : every-human-runs id ≡ ((x : Human) → x runs)
_ = refl


-- зависимость от порядка
-- ======================

-- de dicto

every-human-loves-some-human₁ : Cont Set Set
every-human-loves-some-human₁ = do
  x  ← every
  y  ← some 
  return (x loves y)

_ : every-human-loves-some-human₁ id ≡ ((x : Human) → Σ[ y ∈ Human ] x loves y)
_ = refl

-- de re

every-human-loves-some-human₂ : Cont Set Set
every-human-loves-some-human₂ = do
  x ← some 
  y ← every
  return (y loves x)

_ : every-human-loves-some-human₂ id ≡ (Σ[ x ∈ Human ] ((y : Human) → y loves x))
_ = refl


every-human-loves-some-human₃ : Cont Set Set
every-human-loves-some-human₃ = do
  x ← every
  y ← some 
  return (y loves x)

_ : every-human-loves-some-human₃ id ≡ ((x : Human) → Σ[ y ∈ Human ] y loves x)
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
  x ← some
  return (Ralph believes (x is-spy))

_ : Ralph-believes-some-spy₁ id ≡ (Σ[ x ∈ Human ] Ralph believes (x is-spy))
_ = refl

-- ситуация?
record Bel {a} (h : Human) (A : Set a) (B : A → Set) : Set a where
  field
    s1 : A 
    s2 : h believes (B s1)

infix 2 RB

RB = Bel Ralph

syntax RB A (λ x → B) = RB[ x ∈ A ] B

-- об x : Human, Ральф верит что (k x)
RBelx : Cont Set Human
RBelx k = RB[ x ∈ Human ] k x

Ralph-believes-some-spy₂ : Cont Set Set
Ralph-believes-some-spy₂ = do
  RBelx
  x ← some
  return (x is-spy)

_ : Ralph-believes-some-spy₂ id ≡ (RB[ _ ∈ _ ] Σ[ y ∈ Human ] y is-spy)
_ = refl

-- Определим сокращение: Ральф верит в B
RBel : ∀{a}{A : Set a}(B : Set) → Set a 
RBel {A = A} B = Bel Ralph A (λ _ → B) 

-- тогда:
_ : Ralph-believes-some-spy₂ id ≡ (RBel (Σ[ y ∈ Human ] y is-spy))
_ = refl

Ralph-believes-some-spy₃ : Cont Set Set
Ralph-believes-some-spy₃ = do
  x ← some
  RBelx
  return (x is-spy)

_ : Ralph-believes-some-spy₃ id ≡ (Σ[ x ∈ Human ] RB[ _ ∈ _ ] x is-spy)
_ = refl

_ : Ralph-believes-some-spy₃ id ≡ (Σ[ x ∈ Human ] RBel (x is-spy))
_ = refl

