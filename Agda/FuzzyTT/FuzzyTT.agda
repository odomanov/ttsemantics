module FuzzyTT where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Maybe
open import Data.Product
open import Data.String
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

open import ResiduatedLattices

-- la = Pref
la = Łuk
-- la = Product
MC = Maybe (Carrier la)
MC⊥ = just (LA⊥ la)
MC⊤ = just (LA⊤ la)

-- applying a binary operation to the Maybe label (TODO: rewrite with >>=)
_⟪_⟫_ : MC → ((Carrier la) → (Carrier la) → (Carrier la)) → MC → MC
just v1 ⟪ op ⟫ just v2 = just (op v1 v2)
_ ⟪ _ ⟫ _ = nothing

-- the "or" version of ⟪∙⟫
-- _⟪_⟫⁺_ : MC → ((Carrier la) → (Carrier la) → (Carrier la)) → MC → MC
-- just v1 ⟪ op ⟫⁺ just v2 = just (op v1 v2)
-- nothing ⟪ op ⟫⁺ just v2 = just v2
-- just v1 ⟪ op ⟫⁺ nothing = just v1
-- nothing ⟪ op ⟫⁺ nothing = nothing

-- same for a unary operation
infixr 10 ⟪_⟫_

⟪_⟫_ : ((Carrier la) → (Carrier la)) → MC → MC
⟪ op ⟫ (just v) = just (op v)
⟪ _ ⟫  nothing  = nothing

infixl 10 _⟪⨂⟫_  -- _⟪⨁⟫⁺_

_⟪⨂⟫_ : MC → MC → MC
x ⟪⨂⟫ y = x ⟪ _⊗_ la ⟫ y 

_⟪⇒⟫_ : MC → MC → MC
x ⟪⇒⟫ y = x ⟪ _⇒_ la ⟫ y 

-- _⟪⨁⟫⁺_ : MC → MC → MC
-- x ⟪⨁⟫⁺ y = x ⟪ _⊕_ la ⟫⁺ y 

-- ⟪neg⟫ = ⟪ ⊘ la ⟫_


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


-----------------------------------------------------------------------------

-- Fuzzy Type
record FuzzyTy {ℓ} (A : Set ℓ) : Set (lsuc ℓ) where
  constructor _!_
  field
    fa : A
    fα : MC

open FuzzyTy


-- (Example of) function definition (by defining ffa and ffα):
f : ∀ {l m} → (A : Set l) → (B : A → Set m) → (a : FuzzyTy A) → FuzzyTy (B (fa a))
f {l} {m} = λ (A : Set l) B (a ! α) → ffa A B a ! ffα A (a , α)
  where
  postulate
    ffa : ∀ (A : Set l) (B : A → Set m) → (a : A) → B a
    ffα : ∀ A → A × MC → MC

-- Function application
appl : ∀ {A : Set} {B : Set} (f : FuzzyTy A → FuzzyTy B) → FuzzyTy A → FuzzyTy B
appl f a = (fa (f a)) ! ((fα (f a)) ⟪⨂⟫ (fα a))


-- data FuzzySigma {a b} (A : Set a) (B : A → Set b) : Set (lsuc a ⊔ lsuc b) where
--   _,_ : (a : FuzzyTy A) → FuzzyTy (B (fa a))  → FuzzySigma A B

record FuzzySigma {a b} (A : Set a) (B : A → Set b) : Set (lsuc a ⊔ lsuc b) where
  constructor _,_
  field
    π1 : FuzzyTy A
    π2 : FuzzyTy (B (fa π1)) 

-- when g depends on both x and y
Σ-elimxy : ∀ {l m} {A : Set l} {B : A → Set m} {C : FuzzySigma A B → Set}  
       → (g : (x : FuzzyTy A) → (y : FuzzyTy (B (fa x))) → FuzzyTy (C (x , y)))
       → ((z : FuzzySigma A B) → FuzzyTy (C z))
Σ-elimxy g (z1 , z2) = (fa (g z1 z2)) ! h
  where
  h : MC
  h = ({!fα x!} ⟪⇒⟫ ({!!} ⟪⇒⟫ {!!})) ⟪⨂⟫ ((fα z1) ⟪⨂⟫ (fα z2))
