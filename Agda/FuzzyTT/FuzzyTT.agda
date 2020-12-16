-- Type Theory with fuzzy types

module FuzzyTT where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Empty 
open import Function using (const) 
open import Data.Maybe hiding (_>>=_)
open import Data.Product hiding (_<*>_)
open import Data.Sum
open import Data.Unit
open import Relation.Binary.PropositionalEquality
     using (_≡_; _≢_; refl; cong; subst; subst₂)

open import ResiduatedLattices

-- la = Pref
la = Łuk
-- la = Product

open import FuzzyMonad la  
open Monad MonadFuzzy


record FuzzySigma {a b} (A : Set a) (B : A → Set b) : Set (lsuc a ⊔ lsuc b) where
  constructor _,_
  field
    π1 : Fuzzy A
    π2 : Fuzzy (B (fa π1)) 
open FuzzySigma

Σ-elim : ∀ {l m k} {A : Set l} {B : A → Set m} {C : Σ A B → Set k}  
       → (g : (x : A) (y : (B x)) → Fuzzy (C (x , y)))
       → (z : FuzzySigma A B) → Fuzzy (C (fa (π1 z) , fa (π2 z)))
Σ-elim g (z1 , z2) = join (g <$> z1 <*> z2)


data FuzzySum {a b} (A : Set a) (B : Set b) : Set (lsuc a ⊔ lsuc b) where
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
Empty-elim : ∀ {l} {C : ⊥ → Set l} (f : (x : ⊥) → Fuzzy (C x))
           → (z : Fuzzy ⊥) → Fuzzy (C (fa z))
Empty-elim f z = z >>= f


Unit-elim : ∀ {l} {C : ⊤ → Set l} (c : Fuzzy (C tt))
          → (z : Fuzzy ⊤) → Fuzzy (C (fa z))
Unit-elim c z = z >>= const c          

≡-elim : ∀ {l m} {A : Set l} {C : (x : A) → (y : A) → x ≡ y → Set m}
       → (f : (x : A) → Fuzzy (C x x refl))
       → (ma : Fuzzy A)
       → (mb : Fuzzy A)
       → (p : Fuzzy (fa ma ≡ fa mb))
       → Fuzzy (C (fa ma) (fa mb) (fa p))
≡-elim f ma mb p rewrite (fa p) = f (fa mb)


