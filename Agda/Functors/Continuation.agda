-- Continuation monad -- no transformer
{-# OPTIONS --cumulativity #-}
module _ where

open import Data.Product
open import Data.Unit
open import Function using (_$_; id; flip)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Level 
1ℓ = suc 0ℓ
2ℓ = suc 1ℓ

open import Category.Monad
open import Category.Monad.Indexed
open import Category.Monad.Continuation 

Cont : ∀{a b}(R : Set a) → Set (a ⊔ b) → Set (a ⊔ b)
Cont R = DCont id R R  

MonadICont : ∀{a}{b}(R : Set a) → RawIMonad (DCont {f = a ⊔ b} id)  
MonadICont R = DContIMonad id 


-- проверим монадные законы
module Laws {a} {b} {R : Set a} where

  open RawIMonad (MonadICont {a} {b} R)
  
  unitl : ∀{A B : Set a}{x : A}{f : A → Cont R B}
    → (return x >>= f) ≡ f x
  unitl = refl

  unitr : ∀{A R}{ma : Cont R A}
    → (ma >>= return) ≡ ma
  unitr = refl

  assoc : ∀{A B C : Set a} 
    → {ma : Cont R A} {f : A → Cont R B} {g : B → Cont R C}  
    → ((ma >>= f) >>= g) ≡ (ma >>= (λ a → f a >>= g))
  assoc = refl

  assoc' : ∀{A B C D : Set a} 
    → {f : A → Cont R B} {g : B → Cont R C} {h : C → Cont R D}  
    → ((f >=> g) >=> h) ≡ (f >=> (g >=> h))
  assoc' = refl

  
open RawIMonad (MonadICont Set) 

postulate
  Human   : Set
  John    : Human
  _runs   : Human → Set
  _loves_ : Human → Human → Set

⟦some⟧ : (A : Set) → Cont {1ℓ} Set A
⟦some⟧ A k = Σ[ x ∈ A ] k x

⟦every⟧ : (A : Set) → Cont {1ℓ} Set A
⟦every⟧ A k = ∀(x : A) → k x

⟦someone⟧  = ⟦some⟧  Human
⟦everyone⟧ = ⟦every⟧ Human

⟦John⟧ : Cont Set Human
⟦John⟧ = return John

-- непереходные глаголы

_⟦runs⟧ : Human → Cont Set Set
x ⟦runs⟧ = return (x runs)     

John-runs : Cont Set Set
John-runs = do
  x ← ⟦John⟧
  x ⟦runs⟧
  
_ : John-runs id ≡ (John runs)
_ = refl

someone-runs : Cont Set Set
someone-runs = do
  x ← ⟦someone⟧
  x ⟦runs⟧ 

_ : someone-runs id ≡ (Σ[ x ∈ Human ] x runs)
_ = refl

everyone-runs : Cont Set Set
everyone-runs = do
  x ← ⟦everyone⟧
  x ⟦runs⟧

_ : everyone-runs id ≡ (∀(x : Human) → x runs)
_ = refl


-- переходные глаголы

_⟦loves⟧_ : Human → Human → Cont Set Set
_⟦loves⟧_ x y = return (x loves y)

John-loves-someone : Cont Set Set
John-loves-someone = do
  x ← ⟦John⟧
  y ← ⟦someone⟧
  x ⟦loves⟧ y

_ : John-loves-someone id ≡ (Σ[ x ∈ Human ] John loves x)
_ = refl


-- зависимость от порядка
-- ======================

-- de dicto

everyone-loves-someone : Cont Set Set
everyone-loves-someone = ⟦everyone⟧ >>= (λ x →
                                      ⟦someone⟧ >>= (λ y →
                                                  return (x loves y)))

everyone-loves-someone₁ : Cont Set Set
everyone-loves-someone₁ = do
  x  ← ⟦everyone⟧
  y  ← ⟦someone⟧ 
  x ⟦loves⟧ y

_ : everyone-loves-someone₁ id ≡ ((x : Human) → Σ[ y ∈ Human ] x loves y)
_ = refl


-- de re

everyone-loves-someone₂ : Cont Set Set
everyone-loves-someone₂ = do
  x ← ⟦someone⟧ 
  y ← ⟦everyone⟧
  return (y loves x)

_ : everyone-loves-someone₂ id ≡ (Σ[ x ∈ Human ] (∀(y : Human) → y loves x))
_ = refl


-- belief
-- ======

postulate
  Ralph      : Human
  _is-spy    : Human → Set
  _believes_ : ∀{ℓ} → Human → Set ℓ → Set

-- Ralph believes someone is a spy
-- неясно, как поменять порядок
Ralph-believes-some-spy₁ : Cont Set Set
Ralph-believes-some-spy₁ = do
  x ← ⟦someone⟧
  return (Ralph believes (x is-spy))

_ : Ralph-believes-some-spy₁ id ≡ (Σ[ x ∈ Human ] Ralph believes (x is-spy))
_ = refl

⟦Ralph⟧ : Cont Set Human
⟦Ralph⟧ = return Ralph

_⟦is-spy⟧ : Human → Cont Set Set
x ⟦is-spy⟧ = return (x is-spy)

some-spy : Cont Set Set
some-spy = do      -- ⟦someone⟧ >>= _⟦is-spy⟧
  x ← ⟦someone⟧
  x ⟦is-spy⟧  

_ : some-spy id ≡ Σ Human _is-spy
_ = refl


-- RB аналогично Σ-типу

module m1 where

  -- Ральф верит об s1, что P s1    -- ср. Σ A P
  record RB {a} (A : Set a) (P : A → Set) : Set a where
    field
      s1 : A
      s2 : P s1
  
  infix 2 RB
  syntax RB A (λ x → P) = RB[ x ∈ A ] P 
  
  RBel : Cont Set Human
  RBel = λ k → RB[ x ∈ Human ] k x  --RB Human (λ x → k x)
  
  RBel-some-spy₁ : Cont Set Set
  RBel-some-spy₁ = do
    x ← RBel
    x ⟦is-spy⟧
    
  _ : RBel-some-spy₁ id ≡ (RB Human (λ x → x is-spy))
  _ = refl
    
  _ : RBel-some-spy₁ id ≡ (RB[ x ∈ Human ] x is-spy)
  _ = refl
    
  RBel-some-spy₂ : Cont Set Set
  RBel-some-spy₂ = do
    x ← ⟦someone⟧
    RBel
    x ⟦is-spy⟧
  
  _ : RBel-some-spy₂ id ≡ (Σ[ x ∈ Human ] RB Human (λ _ → x is-spy))
  _ = refl
    
  _ : RBel-some-spy₂ id ≡ (Σ[ x ∈ Human ] RB[ _ ∈ Human ] x is-spy)
  _ = refl
  
  -- Ральф верит, что все шпионы
  RBel-all-spies : Cont Set Set
  RBel-all-spies = do
    RBel 
    x ← ⟦everyone⟧
    x ⟦is-spy⟧
  
  _ : RBel-all-spies id ≡ (RB[ _ ∈ Human ] (∀(x : Human) → x is-spy))
  _ = refl
  
  -- Сокращение: Ральф верит, что B
  RBelp : ∀{a}{A : Set a}(B : Set) → Set a
  RBelp {a}{A} B = RB A (λ _ → B)

  -- RBel-some-spy₁ прямо не переписывается в терминах RBelp, но можно
  -- доказать эквивалентность, причём в общем виде:
  RB→RBelp : ∀{A B} → RB[ x ∈ A ] B → RBelp {A = A} (Σ[ x ∈ A ] B)
  RB→RBelp record { s1 = s1 ; s2 = s2 } = record { s1 = s1 ; s2 = s1 , s2 }

  RBelp→RB : ∀{A B} → RBelp {A = A} (Σ[ x ∈ A ] B) → (RB[ x ∈ A ] B)
  RBelp→RB record { s1 = _ ; s2 = s2 } = record { s1 = proj₁ s2 ; s2 = proj₂ s2 }

  -- остальное переписывается в терминах RBelp
  _ : RBel-some-spy₂ id ≡ (Σ[ x ∈ Human ] RBelp (x is-spy))
  _ = refl
  
  _ : RBel-all-spies id ≡ (RBelp (∀(x : Human) → x is-spy))
  _ = refl


------------------------------------------------------
module m3 where

  postulate
    Unicorn : Set
    _exists : Unicorn → Set

  -- John seeks 
  record S {a}(A : Set a)(P : A → Set) : Set a where
    field
      s1 : A
      s2 : P s1     

  infix 2 S
  syntax S A (λ x → P) = S[ x ∈ A ] P

  Jseek : Cont Set Unicorn
  Jseek = λ k → S[ x ∈ Unicorn ] k x
  
  ⟦someunicorn⟧ : Cont Set Unicorn
  ⟦someunicorn⟧ = ⟦some⟧ Unicorn

  _⟦exists⟧ : Unicorn → Cont Set Set
  x ⟦exists⟧ = return (x exists)

  -- John seeks (a unicorn exists)
  John-seeks-a-unicorn₁ : Cont Set Set
  John-seeks-a-unicorn₁ = do
    x ← ⟦someunicorn⟧
    Jseek
    x ⟦exists⟧
  
  _ : John-seeks-a-unicorn₁ id ≡ (Σ[ x ∈ Unicorn ] S[ _ ∈ _ ] x exists)
  _ = refl
  
  John-seeks-a-unicorn₂ : Cont Set Set
  John-seeks-a-unicorn₂ = do
    Jseek
    x ← ⟦someunicorn⟧
    x ⟦exists⟧

  _ : John-seeks-a-unicorn₂ id ≡ (S[ _ ∈ _ ] Σ[ x ∈ Unicorn ] x exists)
  _ = refl
  
