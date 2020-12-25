-- Type Theory with fuzzy types

open import PersuasionAlgebras

module FuzzyTT {c ℓ₁ ℓ₂} (pa : PersuasionAlgebra c ℓ₁ ℓ₂) where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Empty 
open import Function using (const) 
open import Data.Maybe hiding (_>>=_)
open import Data.Product hiding (_<*>_)
open import Data.Sum
open import Data.Unit
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≡-to-≅)
open import Relation.Binary.PropositionalEquality
     using (_≡_; _≢_; refl; trans)


open import FuzzyMonad pa public
open Monad MonadFuzzy public


record FuzzySigma {a b} (A : Set a) (B : A → Set b) : Set (lsuc c ⊔ lsuc ℓ₁ ⊔ lsuc ℓ₂ ⊔ lsuc a ⊔ lsuc b) where
  constructor _,_
  field
    π1 : Fuzzy A
    π2 : Fuzzy (B (fa π1)) 
open FuzzySigma

Sigma-elim : ∀ {l m k} {A : Set l} {B : A → Set m} {C : Σ A B → Set k}  
       → (g : (x : A) (y : (B x)) → Fuzzy (C (x , y)))
       → (z : FuzzySigma A B) → Fuzzy (C (fa (π1 z) , fa (π2 z)))
Sigma-elim g (z1 , z2) = join (g <$> z1 <*> z2)


data FuzzySum {a b} (A : Set a) (B : Set b) : Set (lsuc c ⊔ lsuc ℓ₁ ⊔ lsuc ℓ₂ ⊔ lsuc a ⊔ lsuc b) where
  finj₁ : Fuzzy A → FuzzySum A B
  finj₂ : Fuzzy B → FuzzySum A B

fa⊎ : ∀ {l m} {A : Set l} {B : Set m} → FuzzySum A B → A ⊎ B
fa⊎ (finj₁ ma) = inj₁ (fa ma)
fa⊎ (finj₂ mb) = inj₂ (fa mb)

Sum-elim : ∀ {l m k} {A : Set l} {B : Set m} {C : A ⊎ B → Set k}
         → (f : (x : A) → Fuzzy (C (inj₁ x)))
         → (g : (x : B) → Fuzzy (C (inj₂ x)))
         → (z : FuzzySum A B) → Fuzzy (C (fa⊎ z))
Sum-elim f g (finj₁ ma) = ma >>= f
Sum-elim f g (finj₂ mb) = mb >>= g


-- The next two basically coincide with the definition of >>=
Empty-elim : ∀ {l} {C : ⊥ → Set l} → (z : Fuzzy ⊥) → Fuzzy (C (fa z))
Empty-elim z = z >>= ⊥-elim


Unit-elim : ∀ {l} {C : ⊤ → Set l} (c : Fuzzy (C tt)) → (z : Fuzzy ⊤) → Fuzzy (C (fa z))
Unit-elim c z = z >>= const c          


-- Another variant of Empty-elim:
Empty-elim' : ∀ {l} {C : ⊥ → Set l}
              → (f : (x : ⊥) → Fuzzy (C x))
              → (z : Fuzzy ⊥) → Fuzzy (C (fa z))
Empty-elim' f z = z >>= f


-- Equality

-- Standard equality elimination (Martin-Lof's axiom J)
J : ∀ {l m} {A : Set l} {C : (x : A) → (y : A) → x ≡ y → Set m}
       → (f : (x : A) → C x x refl)
       → (a : A) → (b : A) → (a≡b : a ≡ b) → C a b a≡b
J f a .a refl = f a

-- Fuzzy equality.
≡-elim : ∀ {l m} {A : Set l} {C : (x : A) → (y : A) → x ≡ y → Set m}
       → (f : (x : A) → Fuzzy (C x x refl))
       → (ma : Fuzzy A)
       → (mb : Fuzzy A)
       → (mp : Fuzzy (fa ma ≡ fa mb))
       → Fuzzy (C (fa ma) (fa mb) (fa mp))
≡-elim {C = C} f ma mb mp = join (J {C = λ x y p → Fuzzy (C x y p)} f <$> ma <*> mb <*> mp)



-- Checking rules for equality

≡-trans : ∀ {l} {A : Set l} {a b c : A} → Fuzzy (a ≡ b) → Fuzzy (b ≡ c) → Fuzzy (a ≡ c)
≡-trans ab bc = trans <$> ab <*> bc


eq1 : ∀ {l} {A B : Set l} → Fuzzy A → A ≡ B → Fuzzy B
eq1 a A≡B rewrite A≡B = a

eq2 : ∀ {l} {A B : Set l} {a b : A}  → Fuzzy (_≡_ {A = A} a b) → A ≡ B → Fuzzy (a ≅ b)
eq2 {l} {A} {B} {a} {b} a≡b A≡B rewrite A≡B = ≡-to-≅ <$> a≡b
