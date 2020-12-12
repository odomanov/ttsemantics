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
record FuzzyTy {l} (A : Set l) : Set (lsuc l) where
  constructor _!_
  field
    fa : A
    fα : MC
open FuzzyTy

-- data FuzzyTy {l} {m} : Set (lsuc l ⊔ lsuc m) where
--   _!_ : ∀ {A : Set l} → A → MC → FuzzyTy   
--   fun : ∀ {A : Set l} {B : A → Set m} → ((x : A) → B x) → FuzzyTy -- ((x : A) → B x)
--   _,_ : ∀ {A : Set l} {B : A → Set m} → (x : A) → B x → FuzzyTy

-- FuzzyTy = ∀ {l} (A : Set l) → A × MC

data FuzzyPi {l m} (A : Set l) (B : A → Set m) : Set (l ⊔ lsuc m) where
  fun : ((x : A) → B x) → ((x : A) → MC) → FuzzyPi A B

_●_ : ∀ {l m} {A : Set l} {B : A → Set m} → FuzzyPi A B → (aα : FuzzyTy A) → FuzzyTy (B (fa aα))
fun f fMC ● aα = (f (fa aα)) ! (fMC (fa aα) ⟪⨂⟫ fα aα)

-- операция, обратная к _●_
toPi : ∀ {l m} {A : Set l} {B : A → Set m} → ((aα : FuzzyTy A) → FuzzyTy (B (fa aα))) → FuzzyPi A B
toPi f = fun (λ x → fa (f (x ! MC⊤))) λ x → fα (f (x ! MC⊤))  -- мы считаем, что результат функции равен
                                                              -- α ⇒ β и *не зависит от α*.  Поэтому
                                                              -- здесь везде может стоять MC⊤!


-- -- (Example of) function definition (by defining ffa and ffα).
-- -- So functions keep the value of ⇒
-- -- f : ∀ {l m} → (A : Set l) → (B : A → Set m) → (aα : FuzzyTy A) → FuzzyTy (B (fa aα))
-- -- f {l} {m} = λ (A : Set l) B (a ! α) → ffa A B a ! ffα A (a , α)
-- --   where
-- --   postulate    -- postulated in the example, but in real life should be defined
-- --     ffa : ∀ (A : Set l) (B : A → Set m) → (a : A) → B a
-- --     ffα : ∀ A → A × MC → MC       -- should give α ⇒ β to make application correct

-- -- _●_ : ∀ {l m} {A : Set l} {B : A → Set m}
-- --          (f : (aα : FuzzyTy A) → FuzzyTy (B (fa aα)))
-- --          → (aα' : FuzzyTy A)
-- --          → FuzzyTy (B (fa aα'))
-- -- f ● aα' = fa (f aα') ! (fα (f aα') ⟪⨂⟫ (fα aα'))

-- -- -- Function type
-- -- data FuzzyFun {l} {m} (A : Set l) (B : A → Set m) : Set (l ⊔ lsuc m) where
-- --   fun : FuzzyTy ((x : A) → B x) → FuzzyFun A B

-- -- -- Function application
-- -- _●_ : ∀ {l m} {A : Set l} {B : A → Set m}
-- --          (f : FuzzyFun A B) 
-- --          → (aα : FuzzyTy A)
-- --          → FuzzyTy (B (fa aα))
-- -- (fun f) ● aα = ((fa f) (fa aα)) ! ((fα f) ⟪⨂⟫ (fα aα))

infixl 4 _●_

record FuzzySigma {a b} (A : Set a) (B : A → Set b) : Set (lsuc a ⊔ lsuc b) where
  constructor _,_
  field
    π1 : FuzzyTy A
    π2 : FuzzyTy (B (fa π1)) 

-- -- when g depends on both x and y
-- Σ-elimxy : ∀ {l m} {A : Set l} {B : A → Set m} {C : FuzzySigma A B → Set}  
--        → (g : (x : FuzzyTy A) → (y : FuzzyTy (B (fa x))) → FuzzyTy (C (x , y)))
--        → ((z : FuzzySigma A B) → FuzzyTy (C z))
-- Σ-elimxy g (z1 , z2) = {!!} --g ● z1 ● z2  -- (fa (g z1 z2)) ! h
--   where
--   h : MC
--   h = ((fα {!!}) ⟪⇒⟫ ((fα {!!}) ⟪⇒⟫ (fα {!!}))) ⟪⨂⟫ ((fα z1) ⟪⨂⟫ (fα z2))

fun2 : ∀ {l m n} {A : Set l} {B : A → Set m} (C : FuzzySigma A B → Set n)
     → FuzzyPi A B
     → FuzzyPi A (λ x → (y : B x) → C (fa {!!} , {!!}))
fun2 = {!!}

-- Σ-elimxy : ∀ {l m} {A : Set l} {B : A → Set m} {C : FuzzySigma A B → Set}  
--        → (g : FuzzyPi A B) → (y : FuzzyTy (B (fa x))) → FuzzyTy (C (x , y)))
--        → ((z : FuzzySigma A B) → FuzzyTy (C z))
-- Σ-elimxy g (z1 , z2) = {!!} --g ● z1 ● z2  -- (fa (g z1 z2)) ! h

