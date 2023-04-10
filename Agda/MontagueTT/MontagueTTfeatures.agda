{-# OPTIONS --overlapping-instances #-}
--{-# OPTIONS --instance-search-depth 50 #-}
-- Montague-like type-theoretical semantics.
-- With coercion through features.

module _ where

open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.Empty
open import Data.List using (List; []; _∷_)
open import Data.Product
open import Function
open import Relation.Nullary renaming (no to not)
open import Relation.Binary.PropositionalEquality
open import Level renaming (zero to lzero; suc to lsuc)

open import Relation.Binary
open import Relation.Binary.Definitions


-- Coercion definitions
-- ==================== 

data _⊆_ {i j} : (A : Set i) → (B : Set j) → Set (lsuc (i ⊔ j)) where
  coerce : {A : Set i} → {B : Set j} → (A → B) → (A ⊆ B)

getfunc : ∀ {i j} → {A : Set i} → {B : Set j} → (A ⊆ B) → (A → B)
getfunc (coerce f) = f

⟪_⟫ : ∀ {i j} {A : Set i} {B : Set j} → A → {{A ⊆ B}} → B
⟪ a ⟫ {{c}} = getfunc c a

⟪→_⟫ : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → (B → C) → {{A ⊆ B}} → (A → C)
⟪→ f ⟫ b = f ⟪ b ⟫ 

⟪Σ⟫ : ∀ {i j k} (A : Set i) {B : Set j} (C : B → Set k) → {{A ⊆ B}} → Set (i ⊔ k)
⟪Σ⟫ A C = Σ A ⟪→ C ⟫

instance
  Idc : ∀ {ℓ} {A : Set ℓ} → A ⊆ A
  Idc = coerce id 
  Prc : ∀{a b} → {A : Set a} → {B : A → Set b} → Σ A B ⊆ A
  Prc = coerce proj₁


-- The structure to hold names
-- ===========================

record LexStructure : Set₁ where
  field
    nameCN namePN nameVI nameVT nameAdj : Set  -- names for syntactic categories
    argPN  : namePN  → nameCN                  -- argument types etc.
    argVI  : nameVI  → nameCN
    argVT  : nameVT  → nameCN × nameCN
    argAdj : nameAdj → nameCN
    _<:0_  : nameCN → nameCN → Set             -- coercion on the syntax level


-- Синтаксис
-- =========

module Syntax (nam : LexStructure) where

  open LexStructure nam 
  
  mutual
  
    data CN : Set where
      cn-n  : nameCN → CN
      cn-ap : {cn₁ : CN} → AP cn₁ → (cn₂ : CN) → {{cn₂ <: cn₁}} → CN
      rcn   : (cn₁ : CN) {cn₂ : CN} → VP cn₂ → {{cn₁ <: cn₂}} → CN    -- CN that VP
      
    data _<:_ : CN → CN → Set where
      instance cnm  : ∀ {n₁ n₂} → {{n₁ <:0 n₂}} → cn-n n₁ <: cn-n n₂
      instance cap  : ∀ {cn₁ cn₂ ap coe} → cn-ap {cn₁} ap cn₂ {{coe}} <: cn₂
      instance crcn : ∀ {cn₁ cn₂ vp coe} → rcn cn₁ {cn₂} vp {{coe}} <: cn₁
      c∘ : ∀ {cn₁ cn₂ cn₃} → cn₁ <: cn₂ → cn₂ <: cn₃ → cn₁ <: cn₃

    data Det : Set where
      a/an every no the ∅ : Det
  
    data VP : (cn : CN) → Set where
      vp-vi : (n : nameVI) → VP $ cn-n $ argVI n
      vp-vt : (n : nameVT) → {cn₂ : CN} → NP cn₂
            → {{coe : cn₂ <: (cn-n (proj₂ (argVT n)))}} → VP (cn-n (proj₁ (argVT n)))
    
    data NP : (cn : CN) → Set where
      np-pn  : (n : namePN) → NP $ cn-n $ argPN n
      np-det : Det → (cn : CN) → NP cn
    
    data AP : (cn : CN) → Set where
      ap-a : (n : nameAdj) → AP $ cn-n $ argAdj n
      
    data S : Set where
      s-nv  : ∀{cn₁} → NP cn₁ → ∀{cn₂} → VP cn₂ → {{coe : cn₁ <: cn₂}} → S


-- Семантика
-- =========

record Model (nam : LexStructure) : Set₁ where
  open LexStructure nam 
  field
    valCN  : nameCN → Set
    valPN  : (n : namePN)  → valCN (argPN n) 
    valVI  : (n : nameVI)  → valCN (argVI n) → Set
    valVT  : (n : nameVT)  → valCN (proj₁ (argVT n))
                           → valCN (proj₂ (argVT n)) → Set
    valAdj : (n : nameAdj) → valCN (argAdj n) → Set
    val<:0 : ∀{n₁ n₂} → {{n₁ <:0 n₂}} → valCN n₁ ⊆ valCN n₂


module Semantics (nam : LexStructure) (m : Model nam) where

  open LexStructure nam 
  open Syntax nam 
  open Model m 

  -- pointed type -- used for defining 'the'
  record Pointed (A : Set) : Set where
    field
      theₚ : A
  open Pointed public    
  
  mutual
  
    -- CN ≠ e → t !  CN это тип.
    ⟦cn_⟧ : CN → Set
    ⟦cn cn-n n ⟧ = valCN n
    ⟦cn cn-ap ap cn {{coe}} ⟧ = ⟪Σ⟫ ⟦cn cn ⟧ ⟦ap ap ⟧ {{⟦coe coe ⟧}}  
    ⟦cn rcn cn₁ {cn₂} vp {{coe}} ⟧ = ⟪Σ⟫ ⟦cn cn₁ ⟧ (⟦vp vp ⟧ {cn₂}) {{⟦coe coe ⟧}} 
  
    ⟦coe_⟧ : {cn₁ cn₂ : CN} → (cn₁ <: cn₂) → (⟦cn cn₁ ⟧ ⊆ ⟦cn cn₂ ⟧)
    ⟦coe cnm ⟧  = val<:0 
    ⟦coe cap ⟧  = coerce proj₁  
    ⟦coe crcn ⟧ = coerce proj₁  
    ⟦coe c∘ c₁₂ c₂₃ ⟧ = coerce (ggetfunc c₂₃ ∘ ggetfunc c₁₂)   
  
    ggetfunc : ∀{cn₁ cn₂} → cn₁ <: cn₂ → ⟦cn cn₁ ⟧ → ⟦cn cn₂ ⟧
    ggetfunc cnm = getfunc val<:0
    ggetfunc cap = proj₁
    ggetfunc crcn = proj₁
    ggetfunc (c∘ c₁₂ c₂₃) = ggetfunc c₂₃ ∘ ggetfunc c₁₂
  
    -- AP = (e → t) 
    ⟦ap_⟧ : {cn : CN} → AP cn → (⟦cn cn ⟧ → Set)
    ⟦ap ap-a n ⟧ = valAdj n
  
    -- NP = (e → t) → t
    ⟦np_⟧ : {cn₁ : CN} → NP cn₁ → {cn₂ : CN} → {{⟦cn cn₁ ⟧ ⊆ ⟦cn cn₂ ⟧}}
          → (⟦cn cn₂ ⟧ → Set) → Set  
    ⟦np np-pn n ⟧           ⟦vp⟧ = ⟦vp⟧ ⟪ valPN n ⟫
    ⟦np np-det d cn ⟧ {cn₂} ⟦vp⟧ = ⟦det d ⟧ cn {cn₂} ⟦vp⟧
    
    -- VP = e → t
    ⟦vp_⟧ : {cn₁ : CN} → VP cn₁ → {cn₂ : CN} → {{⟦cn cn₂ ⟧ ⊆ ⟦cn cn₁ ⟧}}
          → ⟦cn cn₂ ⟧ → Set
    ⟦vp vp-vi n ⟧ x = valVI n ⟪ x ⟫
    ⟦vp vp-vt vt {cn₂} np {{coe}} ⟧ x =
      ⟦np np ⟧ {cn₂} λ y → valVT vt ⟪ x ⟫ $ ⟪ y ⟫ {{⟦coe coe ⟧}} -- λx.(NP (λy.(VT y x)))
  
    -- Det = (e → t) → ((e → t) → t) 
    ⟦det_⟧ : Det → (cn : CN) → {cn₁ : CN} → {{⟦cn cn ⟧ ⊆ ⟦cn cn₁ ⟧}}
           → (⟦cn cn₁ ⟧ → Set) → Set 
    ⟦det a/an ⟧  cn ⟦vp⟧ = Σ ⟦cn cn ⟧ ⟪→ ⟦vp⟧ ⟫ 
    ⟦det every ⟧ cn ⟦vp⟧ = (x : ⟦cn cn ⟧) → ⟦vp⟧ ⟪ x ⟫
    ⟦det no ⟧    cn ⟦vp⟧ = (x : ⟦cn cn ⟧) → ¬ ⟦vp⟧ ⟪ x ⟫ 
    ⟦det the ⟧   cn ⟦vp⟧ = Σ[ Aₚ ∈ Pointed ⟦cn cn ⟧ ] ⟦vp⟧ ⟪ theₚ Aₚ ⟫
    ⟦det ∅ ⟧     cn ⟦vp⟧ = Σ ⟦cn cn ⟧ ⟪→ ⟦vp⟧ ⟫ 
    
    ⟦s_⟧ : S → Set
    ⟦s s-nv {cn₁} np {cn₂} vp {{coe}} ⟧ =
      ⟦np np ⟧ {cn₁} (⟪→ ⟦vp vp ⟧ {cn₂} ⟫ {{⟦coe coe ⟧}})


-- ==================================================================
-- Example1
-- ========

module Ex1 where

  -- Name structure
  
  data nameCN  : Set where Human Dog Animate Object : nameCN
  data namePN  : Set where Alex Mary Polkan : namePN
  data nameVI  : Set where run : nameVI
  data nameVT  : Set where love : nameVT
  data nameAdj : Set where black : nameAdj
  
  argPN : namePN → nameCN
  argPN Alex = Human
  argPN Mary = Human
  argPN Polkan = Dog
  
  argVI : nameVI → nameCN
  argVI run = Animate
  
  argVT : nameVT → nameCN × nameCN
  argVT love = Animate , Object 
  
  argAdj : nameAdj → nameCN
  argAdj black   = Object
  
  
  -- Признаки  -- вообще говоря, относятся к синтаксису
  -- ========
  
  data Feature : Set where f-animate f-dog f-human f-object : Feature
  
  -- the order itself is arbitrary (not important)
  data _<_ : Feature → Feature → Set where
    a<o : f-animate < f-object
    h<a : f-human < f-animate
    h<o : f-human < f-object
    d<h : f-dog < f-human
    d<a : f-dog < f-animate
    d<o : f-dog < f-object
    
  <-trans : ∀ {i j k} → i < j → j < k → i < k
  <-trans h<a a<o = h<o
  <-trans d<h h<a = d<a
  <-trans d<h h<o = d<o
  <-trans d<a a<o = d<o
  
  isSTO : IsStrictTotalOrder _≡_ _<_
  isSTO = record { isEquivalence = isEquivalence
                 ; trans = <-trans
                 ; compare = cmp }
    where
    cmp : Trichotomous _≡_ _<_
    cmp f-animate f-animate = tri≈ (λ ()) refl (λ ())
    cmp f-animate f-dog     = tri> (λ ()) (λ ()) d<a
    cmp f-animate f-human   = tri> (λ ()) (λ ()) h<a
    cmp f-animate f-object  = tri< a<o (λ ()) (λ ())
    cmp f-dog     f-animate = tri< d<a (λ ()) (λ ())
    cmp f-dog     f-dog     = tri≈ (λ ()) refl (λ ())
    cmp f-dog     f-human   = tri< d<h (λ ()) (λ ())
    cmp f-dog     f-object  = tri< d<o (λ ()) (λ ())
    cmp f-human   f-animate = tri< h<a (λ ()) (λ ())
    cmp f-human   f-dog     = tri> (λ ()) (λ ()) d<h
    cmp f-human   f-human   = tri≈ (λ ()) refl (λ ())
    cmp f-human   f-object  = tri< h<o (λ ()) (λ ())
    cmp f-object  f-animate = tri> (λ ()) (λ ()) a<o
    cmp f-object  f-dog     = tri> (λ ()) (λ ()) d<o
    cmp f-object  f-human   = tri> (λ ()) (λ ()) h<o
    cmp f-object  f-object  = tri≈ (λ ()) refl (λ ())


  -- feature definitions should be in a separate module but this slows down
  -- the whole thing

  open IsStrictTotalOrder isSTO 
  
  FS = List Feature       -- feature sets
  
  -- insert guarantees 1) order, 2) uniqueness
  insert : Feature → FS → FS
  insert x [] = x ∷ []
  insert x (f ∷ fs) with compare x f
  ... | tri< a ¬b ¬c = f ∷ insert x fs
  ... | tri≈ ¬a b ¬c = f ∷ fs
  ... | tri> ¬a ¬b c = x ∷ f ∷ fs
  
  -- subset for FS, works properly only for ordered FS
  data _⊆ᶠ_ : FS → FS → Set where
    instance sub∅  : [] ⊆ᶠ []
    instance sub1  : ∀{fs₁ fs₂ f} → {{fs₁ ⊆ᶠ fs₂}} → fs₁ ⊆ᶠ (f ∷ fs₂)  
    instance sub2  : ∀{fs₁ fs₂ f} → {{fs₁ ⊆ᶠ fs₂}} → (f ∷ fs₁) ⊆ᶠ (f ∷ fs₂)  
  
  -- some properties
  
  []-⊆ᶠ-f : ∀{fs} → [] ⊆ᶠ fs
  []-⊆ᶠ-f {[]} = sub∅
  []-⊆ᶠ-f {x ∷ fs} = sub1 {_} {fs} {{[]-⊆ᶠ-f {fs}}}
  
  sub1ʳ : ∀{fs₁ fs₂ f₁} → (f₁ ∷ fs₁) ⊆ᶠ fs₂ → fs₁ ⊆ᶠ fs₂
  sub1ʳ {[]} {_ ∷ _} _ = []-⊆ᶠ-f
  sub1ʳ (sub1 {{p}}) = sub1 {{sub1ʳ p}}
  sub1ʳ sub2 = sub1

  lem1 : ∀{f fs₁ fs₂ fs₃} → fs₁ ⊆ᶠ fs₃ → (f ∷ fs₃) ⊆ᶠ fs₂ → (f ∷ fs₁) ⊆ᶠ fs₂
  lem1 sub∅ sub1 = sub1 
  lem1 sub∅ sub2 = sub2
  lem1 (sub1 {{q₁}}) (sub1 {{sub1 {{q₂}} }}) = sub1 ⦃ sub1 {{lem1 q₁ (tmp q₂)}} ⦄
    where
    tmp : ∀{f f₂ fs₂ fs₃} → (f ∷ f₂ ∷ fs₂) ⊆ᶠ fs₃ → (f ∷ fs₂) ⊆ᶠ fs₃
    tmp (sub1 {{r}}) = sub1 {{tmp r}}
    tmp (sub2 {{r}}) = sub2 {{sub1ʳ r}}
  lem1 (sub1 {{q₁}}) (sub1 {{sub2 {{q₂}} }}) = sub1 ⦃ sub2 {{sub1ʳ (lem1 q₁ q₂)}} ⦄
  lem1 (sub1 {{q₁}}) (sub2 {{q₂}}) = sub2 {{sub1ʳ (lem1 q₁ q₂)}}
  lem1 (sub2 {{q₁}}) (sub1 {{q₂}}) = sub1 {{lem1 (sub2 {{q₁}}) q₂}}
  lem1 (sub2 {{q₁}}) (sub2 {{q₂}}) = sub2 {{lem1 q₁ q₂}}


  -- check that ⊆ᶠ is partial order
  
  ⊆ᶠ-refl : ∀{fs} → fs ⊆ᶠ fs
  ⊆ᶠ-refl {[]} = sub∅
  ⊆ᶠ-refl {_ ∷ _} = sub2 {{⊆ᶠ-refl}} 
  
  ⊆ᶠ-trans : ∀{fs₁ fs₂ fs₃} → fs₁ ⊆ᶠ fs₂ → fs₂ ⊆ᶠ fs₃ → fs₁ ⊆ᶠ fs₃
  ⊆ᶠ-trans sub∅ sub∅ = sub∅
  ⊆ᶠ-trans sub∅ sub1 = sub1
  ⊆ᶠ-trans (sub1 {{p₁}}) (sub1 {{p₂}}) = sub1 {{⊆ᶠ-trans p₁ (sub1ʳ p₂)}}
  ⊆ᶠ-trans (sub1 {{p₁}}) (sub2 {{p₂}}) = sub1 {{⊆ᶠ-trans p₁ p₂}}
  ⊆ᶠ-trans (sub2 {{p₁}}) (sub1 {{p₂}}) = sub1 {{lem1 p₁ p₂}}
  ⊆ᶠ-trans (sub2 {{p₁}}) (sub2 {{p₂}}) = sub2 {{⊆ᶠ-trans p₁ p₂}}

  ⊆ᶠ-asym  : ∀{fs₁ fs₂} → fs₁ ⊆ᶠ fs₂ → fs₂ ⊆ᶠ fs₁ → fs₁ ≡ fs₂
  ⊆ᶠ-asym sub∅ sub∅ = refl
  ⊆ᶠ-asym (sub1 {{p₁}}) (sub1 {{p₂}}) = ⊥-elim (pp p₁ p₂)
    where
    pp : ∀{f₁ f₂ fs₁ fs₂} → (f₁ ∷ fs₁) ⊆ᶠ fs₂ → (f₂ ∷ fs₂) ⊆ᶠ fs₁ → ⊥
    pp (sub1 {{q₁}}) (sub1 {{q₂}}) = pp q₁ (sub1 {{sub1ʳ q₂}})
    pp (sub1 {{q₁}}) (sub2 {{q₂}}) = pp q₁ (sub1 {{q₂}})
    pp (sub2 {{q₁}}) (sub1 {{q₂}}) = pp (sub1 {{q₁}}) q₂
    pp (sub2 {{q₁}}) (sub2 {{q₂}}) = pp q₁ q₂
  ⊆ᶠ-asym (sub1 {{x}}) (sub2 {{y}}) = cong₂ _∷_ refl (⊆ᶠ-asym (sub1ʳ x) y)
  ⊆ᶠ-asym (sub2 {{x}}) (sub1 {{y}}) = cong₂ _∷_ refl (⊆ᶠ-asym x (sub1ʳ y))
  ⊆ᶠ-asym (sub2 {{x}}) (sub2 {{y}}) = cong₂ _∷_ refl (⊆ᶠ-asym x y)
  
  
  -- feature sets for types
  
  FO : FS
  FO = insert f-object []
  
  FA : FS
  FA = insert f-animate FO
  
  FH : FS
  FH = insert f-human FA
  
  FD : FS
  FD = insert f-dog FA
  
  -- Some tests
  
  _ : FO ≡ f-object ∷ []
  _ = refl
  
  _ : FA ≡ f-object ∷ f-animate ∷ []
  _ = refl
  
  _ : FH ≡ f-object ∷ f-animate ∷ f-human ∷ []
  _ = refl
  
  _ : FD ≡ f-object ∷ f-animate ∷ f-dog ∷ []
  _ = refl
  
  
  _ : [] ⊆ᶠ [] 
  _ = it
  
  _ : [] ⊆ᶠ FH
  _ = it
  
  _ : FO ⊆ᶠ FA
  _ = it
  
  _ : FO ⊆ᶠ FH
  _ = it
  
  _ : FO ⊆ᶠ FO
  _ = it
  
  _ : FA ⊆ᶠ FD
  _ = it
  
  _ : FA ⊆ᶠ FH
  _ = it
  
  
  -- Connect names and feature sets
  
  FSet : nameCN → FS
  FSet Human   = FH
  FSet Dog     = FD
  FSet Animate = FA
  FSet Object  = FO
  
  -- Syntax level coercion for basic types/names
  _<:0_ : nameCN → nameCN → Set
  n₁ <:0 n₂ = FSet n₂ ⊆ᶠ FSet n₁
  
  -- Tests
  
  _ : Human <:0 Animate
  _ = it 
  
  _ : Dog <:0 Object
  _ = it 
  
  _ : Dog <:0 Dog
  _ = it 
  
  
  NS : LexStructure
  NS = record { nameCN = nameCN; namePN = namePN; nameVI = nameVI
              ; nameVT = nameVT; nameAdj = nameAdj
              ; argPN = argPN; argVI = argVI; argVT = argVT; argAdj = argAdj
              ; _<:0_ = _<:0_
              }
  
  
  
  -- Семантика
  -- =========
  
  -- The type of objects having features FS
  data ⟦CN⟧ : FS → Set where
    base : (n : namePN) → ⟦CN⟧ $ FSet $ argPN n
    ⦅_⦆  : ∀ {f₁ f₂} → {{f₂ ⊆ᶠ f₁}} → ⟦CN⟧ f₁ → ⟦CN⟧ f₂ -- with features f₂ and more
  
  -- the same ⟦CN⟧ fs for the same fs
  uniq-⟦CN⟧ : ∀{fs₁ fs₂} → fs₁ ≡ fs₂ → ⟦CN⟧ fs₁ ≡ ⟦CN⟧ fs₂
  uniq-⟦CN⟧ refl = refl
  
  -- cannot be proven in general!
  -- uniq' : ∀{fs₁ fs₂} → ⟦CN⟧ fs₁ ≡ ⟦CN⟧ fs₂ → fs₁ ≡ fs₂ 

  -- Useful aliases
  
  *Human   = ⟦CN⟧ FH
  *Dog     = ⟦CN⟧ FD
  *Animate = ⟦CN⟧ FA
  *Object  = ⟦CN⟧ FO
  
  *Alex   = base Alex
  *Mary   = base Mary
  *Polkan = base Polkan
  
  
  -- Tests
  
  -- *Mary is a member of all higher ⟦CN⟧s
  _ : *Human
  _ = *Mary
  
  _ : *Human
  _ = ⦅ *Mary ⦆
  
  _ : *Animate
  _ = ⦅ *Mary ⦆
  
  _ : *Object
  _ = ⦅ *Mary ⦆
  
  _ : *Object
  _ = ⦅ *Polkan ⦆
  
  postulate
    _*run   : *Animate → Set
    _*love_ : *Animate → *Object → Set
    *black  : *Object → Set
  
  ⦅→_⦆ : ∀{fs₁ fs₂} → (⟦CN⟧ fs₁ → Set) → {{fs₁ ⊆ᶠ fs₂}} → (⟦CN⟧ fs₂ → Set)
  ⦅→ f ⦆ x = f ⦅ x ⦆
  
  _ : *Human → Set
  _ = λ x → ⦅ x ⦆ *run
  
  _ : *Dog → Set
  _ = ⦅→ _*run ⦆ 
  
  
  -- Names valuation
  
  valCN : nameCN → Set
  valCN n = ⟦CN⟧ (FSet n)
  
  valPN  : (n : namePN)  → valCN (argPN n)
  valPN n = base n
  
  valVI  : (n : nameVI)  → valCN (argVI n) → Set
  valVI run = _*run
  
  valVT  : (n : nameVT)  → valCN (proj₁ (argVT n)) → valCN (proj₂ (argVT n)) → Set
  valVT love = _*love_
  
  valAdj : (n : nameAdj) → valCN (argAdj n) → Set
  valAdj black = *black
  
  val<:0 : ∀{n₁ n₂} → {{n₁ <:0 n₂}} → valCN n₁ ⊆ valCN n₂
  val<:0 = coerce ⦅_⦆
  
  _ : ∀{fs} → ⟦CN⟧ fs → ⟦CN⟧ []
  _ = ⦅_⦆ {{[]-⊆ᶠ-f}}
  
  M : Model NS
  M = record { valCN  = valCN
             ; valPN  = valPN
             ; valVI  = valVI
             ; valVT  = valVT
             ; valAdj = valAdj
             ; val<:0 = λ {n₁} {n₂} → val<:0 {n₁} {n₂}
             }
  
  open Syntax NS hiding (cnm; _<:_) -- hide redundant instances
  open Semantics NS M 
  
 
  -- Expression examples
  -- ===================
  
  
  s1 = s-nv (np-pn Mary) (vp-vi run) 
  
  _ : ⟦s s1 ⟧ ≡  ⦅ *Mary ⦆ *run
  _ = refl
  
  
  s2 = s-nv (np-pn Polkan) (vp-vi run) 
  
  _ : ⟦s s2 ⟧ ≡  ⦅ *Polkan ⦆ *run
  _ = refl
  
  
  -- a human runs
  s3 = s-nv (np-det a/an (cn-n Human)) (vp-vi run) 
  
  -- _ : ⟦s s3 ⟧ ≡ ⟪Σ⟫ *Human ⦅→ _*run ⦆ 
  -- _ = refl
  
  _ : ⟦s s3 ⟧ ≡ Σ *Human (λ x → ⦅ x ⦆ *run)             --⟪Σ⟫ *Human _*run 
  _ = refl
  
  _ : ⟦s s3 ⟧ ≡ Σ *Human ⦅→ _*run ⦆    
  _ = refl
  
  
  -- every human runs
  s4 = s-nv (np-det every (cn-n Human)) (vp-vi run)
  
  _ : ⟦s s4 ⟧ ≡ ((x : *Human) → ⦅ x ⦆ *run)
  _ = refl
  
  
  -- the human runs
  s5 = s-nv (np-det the (cn-n Human)) (vp-vi run)
  
  _ : ⟦s s5 ⟧ ≡ (Σ[ Aₚ ∈ Pointed *Human ] ⦅ theₚ Aₚ ⦆ *run)
  _ = refl
  
  _ : ⟦s s5 ⟧
  _ = Hₚ , *Mary-run
    where
    Hₚ : Pointed *Human 
    Hₚ = record { theₚ = *Mary }
  
    postulate *Mary-run : ⦅ *Mary ⦆ *run
  
  
  -- Mary loves Alex
  
  loves-Alex : VP _
  loves-Alex = vp-vt love (np-pn Alex)
  
  s6 = s-nv (np-pn Mary) loves-Alex
  
  _ : ⟦s s6 ⟧ ≡ ⦅ *Mary ⦆ *love ⦅ *Alex ⦆
  _ = refl
  
  
  -- Mary loves Polkan
  
  s7 = s-nv (np-pn Mary) (vp-vt love (np-pn Polkan))
  
  _ : ⟦s s7 ⟧ ≡ ⦅ *Mary ⦆ *love ⦅ *Polkan ⦆ 
  _ = refl
  
  
  -- Прилагательные / свойства
  
  postulate
    *polkan-is-black : *black ⦅ *Polkan ⦆
    *polkan-runs : ⦅ *Polkan ⦆ *run
  
  black-dog = cn-ap (ap-a black) (cn-n Dog)
  
  *black-dog : ⟦cn black-dog ⟧
  *black-dog = *Polkan , *polkan-is-black 

  -- a black dog runs
  s8 = s-nv (np-det a/an black-dog) (vp-vi run) {{c∘ cap it}}

  _ : ⟦s s8 ⟧ ≡ (Σ[ bd ∈ (Σ[ b ∈ *Dog ] *black ⦅ b ⦆) ] ⦅ proj₁ bd ⦆ *run)
  _ = refl

  _ : ⟦s s8 ⟧
  _ = (*Polkan , *polkan-is-black) , *polkan-runs

  
  -- Относительные конструкции (CN that VP и пр.)
  
  human-that-runs : CN
  human-that-runs = rcn (cn-n Human) (vp-vi run)

  _ : ⟦cn human-that-runs ⟧ ≡ (Σ[ h ∈ *Human ] ⦅ h ⦆ *run)
  _ = refl

  _ : ⟦cn human-that-runs ⟧
  _ = *Mary , *Mary-runs
    where postulate *Mary-runs : ⦅ *Mary ⦆ *run 
  
  
  a-human-that-runs : NP _ 
  a-human-that-runs = np-det a/an human-that-runs

  -- a human that runs runs
  s9 = s-nv a-human-that-runs (vp-vi run) {{c∘ crcn it}} 
  
  
  -- Mary loves a human that runs
  
  s10 = s-nv (np-pn Mary) (vp-vt love a-human-that-runs 
                                 {{c∘ ((c∘ {cn₃ = (cn-n Animate)} crcn it)) it}}
                                 -- {{c∘ ((c∘ crcn (Syntax.cnm {n₂ = Animate}))) Syntax.cnm}}
                          )
  
  -- beware! with --overlapping-instances the search is very slow without hints
  _ : ⟦s s10 ⟧ ≡ (Σ[ hr ∈ Σ[ h ∈ *Human ] ⦅ h ⦆ *run ] ⦅ *Mary ⦆ *love (⦅_⦆ {{sub2}} ⦅ proj₁ hr ⦆))
  _ = refl
  


-- ==================================================================
-- Example2
-- ========

module Ex2 where

  -- Name structure
  
  data nameCN  : Set where Human Info Phys Book : nameCN
  data namePN  : Set where John War-and-Peace : namePN
  data nameVI  : Set where 
  data nameVT  : Set where take read : nameVT
  data nameAdj : Set where
  
  argPN : namePN → nameCN
  argPN John = Human
  argPN War-and-Peace = Book
  
  argVI : nameVI → nameCN
  argVI ()
  
  argVT : nameVT → nameCN × nameCN
  argVT take = Human , Phys
  argVT read = Human , Info
  
  argAdj : nameAdj → nameCN
  argAdj ()
  
  
  -- Признаки  -- вообще говоря, относятся к синтаксису
  -- ========
  
  data Feature : Set where f-info f-phys f-human : Feature
  
  -- the order itself is arbitrary (not important)
  data _<_ : Feature → Feature → Set where
    i<p : f-info < f-phys
    i<h : f-info < f-human
    p<h : f-phys < f-human
    
  <-trans : ∀ {i j k} → i < j → j < k → i < k
  <-trans i<p p<h = i<h
  <-trans i<h ()
  <-trans p<h ()
  
  isSTO : IsStrictTotalOrder _≡_ _<_
  isSTO = record { isEquivalence = isEquivalence
                 ; trans = <-trans
                 ; compare = cmp }
    where
    cmp : Trichotomous _≡_ _<_
    cmp f-info f-info = tri≈ (λ ()) refl (λ ())
    cmp f-info f-phys = tri< i<p (λ ()) (λ ())
    cmp f-info f-human = tri< i<h (λ ()) (λ ())
    cmp f-phys f-info = tri> (λ ()) (λ ()) i<p
    cmp f-phys f-phys = tri≈ (λ ()) refl (λ ())
    cmp f-phys f-human = tri< p<h (λ ()) (λ ())
    cmp f-human f-info = tri> (λ ()) (λ ()) i<h
    cmp f-human f-phys = tri> (λ ()) (λ ()) p<h
    cmp f-human f-human = tri≈ (λ ()) refl (λ ())


  -- feature definitions should be in a separate module but this slows down
  -- the whole thing

  open IsStrictTotalOrder isSTO 
  
  FS = List Feature       -- feature sets
  
  -- insert guarantees 1) order, 2) uniqueness
  insert : Feature → FS → FS
  insert x [] = x ∷ []
  insert x (f ∷ fs) with compare x f
  ... | tri< a ¬b ¬c = f ∷ insert x fs
  ... | tri≈ ¬a b ¬c = f ∷ fs
  ... | tri> ¬a ¬b c = x ∷ f ∷ fs
  
  -- subset for FS, works properly only for ordered FS
  data _⊆ᶠ_ : FS → FS → Set where
    instance sub∅ : [] ⊆ᶠ []
    instance sub1 : ∀{fs₁ fs₂ f} → {{fs₁ ⊆ᶠ fs₂}} → fs₁ ⊆ᶠ (f ∷ fs₂)  
    instance sub2 : ∀{fs₁ fs₂ f} → {{fs₁ ⊆ᶠ fs₂}} → (f ∷ fs₁) ⊆ᶠ (f ∷ fs₂)  
  
  -- some properties
  
  []-⊆ᶠ-f : ∀{fs} → [] ⊆ᶠ fs
  []-⊆ᶠ-f {[]} = sub∅
  []-⊆ᶠ-f {x ∷ fs} = sub1 {_} {fs} {{[]-⊆ᶠ-f {fs}}}
  
  ⊆ᶠ-refl : ∀{fs} → fs ⊆ᶠ fs
  ⊆ᶠ-refl {[]} = sub∅
  ⊆ᶠ-refl {x ∷ fs} = sub2 {{⊆ᶠ-refl}} 
  
  sub1ʳ : ∀{fs₁ fs₂ f₁} → (f₁ ∷ fs₁) ⊆ᶠ fs₂ → fs₁ ⊆ᶠ fs₂
  sub1ʳ {[]} {_ ∷ _} _ = []-⊆ᶠ-f
  sub1ʳ (sub1 {{p}}) = sub1 {{sub1ʳ p}}
  sub1ʳ sub2 = sub1
   
  
  -- feature sets for types
  
  FI : FS
  FI = insert f-info []
  
  FP : FS
  FP = insert f-phys []
  
  FB : FS
  FB = insert f-phys FI
  
  FH : FS
  FH = insert f-human []
  
  -- Some tests
  
  _ : FI ≡ f-info ∷ []
  _ = refl
  
  _ : FP ≡ f-phys ∷ []
  _ = refl
  
  _ : FH ≡ f-human ∷ []
  _ = refl
  
  _ : FB ≡ f-phys ∷ f-info ∷ []
  _ = refl
  
  
  _ : [] ⊆ᶠ [] 
  _ = sub∅
  
  _ : [] ⊆ᶠ FH
  _ = sub1
  
  _ : [] ⊆ᶠ FB
  _ = sub1 
  
  _ : FI ⊆ᶠ (f-info ∷ [])
  _ = sub2
  
  _ : FP ⊆ᶠ FB
  _ = sub2 
  
  _ : FI ⊆ᶠ FB
  _ = sub1 
  
  
  -- Connect names and feature sets
  
  FSet : nameCN → FS
  FSet Info  = FI
  FSet Phys  = FP
  FSet Book  = FB
  FSet Human = FH
  
  -- Syntax level coercion for basic types/names
  _<:0_ : nameCN → nameCN → Set
  n₁ <:0 n₂ = FSet n₂ ⊆ᶠ FSet n₁
  
  -- Tests
  
  _ : Book <:0 Info
  _ = sub1 
  
  _ : Book <:0 Phys
  _ = sub2
  
  _ : Info <:0 Info
  _ = ⊆ᶠ-refl 
  
  
  NS : LexStructure
  NS = record { nameCN = nameCN; namePN = namePN; nameVI = nameVI
              ; nameVT = nameVT; nameAdj = nameAdj
              ; argPN = argPN; argVI = argVI; argVT = argVT; argAdj = argAdj
              ; _<:0_ = _<:0_
              }
  
  
  
  -- Семантика
  -- =========
  
  -- The type of objects having features FS
  data ⟦CN⟧ : FS → Set where
    base : (n : namePN) → ⟦CN⟧ (FSet (argPN n))
    ⦅_⦆  : ∀ {f₁ f₂} → {{f₂ ⊆ᶠ f₁}} → ⟦CN⟧ f₁ → ⟦CN⟧ f₂ 
  
  -- the same ⟦CN⟧ fs for the same fs
  uniq-⟦CN⟧ : ∀{fs₁ fs₂} → fs₁ ≡ fs₂ → ⟦CN⟧ fs₁ ≡ ⟦CN⟧ fs₂
  uniq-⟦CN⟧ refl = refl
  
  -- cannot be proven in general!
  -- uniq' : ∀{fs₁ fs₂} → ⟦CN⟧ fs₁ ≡ ⟦CN⟧ fs₂ → fs₁ ≡ fs₂ 
  
  
  -- Useful aliases
  
  *Human = ⟦CN⟧ FH
  *Info  = ⟦CN⟧ FI
  *Phys  = ⟦CN⟧ FP
  *Book  = ⟦CN⟧ FB
  
  *John = base John
  *War-and-Peace  = base War-and-Peace
  
  
  -- Tests
  
  -- *War-and-Peace is a member of all higher ⟦CN⟧s
  _ : *Book
  _ = *War-and-Peace
  
  _ : *Info
  _ = ⦅ *War-and-Peace ⦆
  
  _ : *Phys
  _ = ⦅ *War-and-Peace ⦆
  
  
  postulate
    _*take_ : *Human → *Phys → Set
    _*read_ : *Human → *Info → Set
  
  
  -- Valuation for names
  
  valCN : nameCN → Set
  valCN n = ⟦CN⟧ (FSet n)
  
  valPN  : (n : namePN)  → valCN (argPN n)
  valPN n = base n
  
  valVI  : (n : nameVI)  → valCN (argVI n) → Set
  valVI ()
  
  valVT  : (n : nameVT)  → valCN (proj₁ (argVT n)) → valCN (proj₂ (argVT n)) → Set
  valVT take = _*take_
  valVT read = _*read_
  
  valAdj : (n : nameAdj) → valCN (argAdj n) → Set
  valAdj ()
  
  val<:0 : ∀{n₁ n₂} → {{n₁ <:0 n₂}} → valCN n₁ ⊆ valCN n₂
  val<:0 = coerce ⦅_⦆
  
  M : Model NS
  M = record { valCN  = valCN
             ; valPN  = valPN
             ; valVI  = valVI
             ; valVT  = valVT
             ; valAdj = valAdj
             ; val<:0 = λ {n₁} {n₂} → val<:0 {n₁} {n₂}
             }
  
  open Syntax NS hiding (cnm; _<:_) -- hide redundant instances
  open Semantics NS M 
  
  
  
  -- Expression examples
  -- ===================
  
  s1 = s-nv (np-pn John) (vp-vt take (np-pn War-and-Peace)) 
  
  _ : ⟦s s1 ⟧ ≡ ⦅ *John ⦆ *take ⦅ *War-and-Peace ⦆
  _ = refl 
  
  s2 = s-nv (np-pn John) (vp-vt read (np-pn War-and-Peace)) 
  
  _ : ⟦s s2 ⟧ ≡ ⦅ *John ⦆ *read ⦅ *War-and-Peace ⦆
  _ = refl
  
  -- John take a book
  s3 = s-nv (np-pn John) (vp-vt take (np-det a/an (cn-n Book)))
  
  _ : ⟦s s3 ⟧ ≡ Σ *Book λ b → ⦅ *John ⦆ *take ⦅ b ⦆
  _ = refl
  
  _ : ⟦s s3 ⟧ ≡ (Σ[ b ∈ *Book ] ⦅ *John ⦆ *take ⦅ b ⦆)
  _ = refl
  
  -- John read every book
  s4 = s-nv (np-pn John) (vp-vt read (np-det every (cn-n Book)))
  
  _ : ⟦s s4 ⟧ ≡ ∀ (b : *Book) →  ⦅ *John ⦆ *read ⦅ b ⦆
  _ = refl
  
  
