module FuzzyTT where

open import Data.Maybe
open import Data.String
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

open import ResiduatedLattices

-- la = Pref
la = Łuk
-- la = Product
MC = Maybe (Carrier la)
MC⊥ = just (LA⊥ la)
MC⊤ = just (LA⊤ la)

data Var : Set where
  x y z : Var

data Universe : Set where
  U₁ U₂ U₃ : Universe
  
data Type : Set where
  A B C D : Type
  ⊤ ⊥ : Type
  Sigma : Var → Type → Type
  Pi : Var → Type → Type

data Judgment : Set₁ 

data Context : Set₁ where
  ∅ : Context
  _,_ : Context → Judgment → Context
  
data Judgment where
  -- _⦂_ : Var → Type → Judgment
  -- _!_⦂_ : Var → MC → Type → Judgment
  _!_⦂_ : {A : Set}(a : A) → MC → (B : Set) → {{A ≡ B}} → Judgment

_⦂_ : {A : Set}(a : A) → (B : Set) → {{A ≡ B}} → Judgment 
tm ⦂ Ty = tm ! MC⊤ ⦂ Ty

postulate
  AA : Set
  aa : AA

_ : AA ≡ AA
_ = refl

a = aa ! MC⊥ ⦂ AA
