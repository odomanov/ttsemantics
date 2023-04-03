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

record NameStructure : Set₁ where
  field
    nameCN namePN nameVI nameVT nameAdj : Set  -- names for syntactic categories
    argPN  : namePN  → nameCN                  -- argument types etc.
    argVI  : nameVI  → nameCN
    argVT  : nameVT  → nameCN × nameCN
    argAdj : nameAdj → nameCN
    _<:0_  : nameCN → nameCN → Set             -- coercion on the syntax level


-- Синтаксис
-- =========

module Syntax (nam : NameStructure) where

  open NameStructure nam 
  
  mutual
  
    data CN : Set where
      cn-n  : nameCN → CN
      cn-ap : {cn1 : CN} → AP cn1 → (cn2 : CN) → {{cn2 <: cn1}} → CN
      rcn   : (cn1 : CN) {cn2 : CN} → VP cn2 → {{cn1 <: cn2}} → CN    -- CN that VP
      
    data _<:_ : CN → CN → Set where
      instance cnm  : ∀ {n1 n2} → {{n1 <:0 n2}} → cn-n n1 <: cn-n n2
      instance cap  : ∀ {cn1 cn2 ap coe} → cn-ap {cn1} ap cn2 {{coe}} <: cn2
      instance crcn : ∀ {cn1 cn2 vp coe} → rcn cn1 {cn2} vp {{coe}} <: cn1
      c∘ : ∀ {cn1 cn2 cn3} → cn1 <: cn2 → cn2 <: cn3 → cn1 <: cn3

    data Det : Set where
      a/an every no the ∅ : Det
  
    data VP : (cn : CN) → Set where
      vp-vi : (n : nameVI) → VP $ cn-n $ argVI n
      vp-vt : (n : nameVT) → {cn2 : CN} → NP cn2
            → {{coe : cn2 <: (cn-n (proj₂ (argVT n)))}} → VP (cn-n (proj₁ (argVT n)))
    
    data NP : (cn : CN) → Set where
      np-pn  : (n : namePN) → NP $ cn-n $ argPN n
      np-det : Det → (cn : CN) → NP cn
    
    data AP : (cn : CN) → Set where
      ap-a : (n : nameAdj) → AP $ cn-n $ argAdj n
      
    data S : Set where
      s-nv  : ∀{cn1} → NP cn1 → ∀{cn2} → VP cn2 → {{coe : cn1 <: cn2}} → S


-- Семантика
-- =========

record Model (nam : NameStructure) : Set₁ where
  open NameStructure nam 
  field
    valCN  : nameCN → Set
    valPN  : (n : namePN)  → valCN (argPN n) 
    valVI  : (n : nameVI)  → valCN (argVI n) → Set
    valVT  : (n : nameVT)  → valCN (proj₁ (argVT n))
                           → valCN (proj₂ (argVT n)) → Set
    valAdj : (n : nameAdj) → valCN (argAdj n) → Set
    val<:0 : ∀{n1 n2} → {{n1 <:0 n2}} → valCN n1 ⊆ valCN n2


module Semantics (nam : NameStructure) (m : Model nam) where

  open NameStructure nam 
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
    ⟦cn rcn cn1 {cn2} vp {{coe}} ⟧ = ⟪Σ⟫ ⟦cn cn1 ⟧ (⟦vp vp ⟧ {cn2}) {{⟦coe coe ⟧}} 
  
    ⟦coe_⟧ : {cn1 cn2 : CN} → (cn1 <: cn2) → (⟦cn cn1 ⟧ ⊆ ⟦cn cn2 ⟧)
    ⟦coe cnm ⟧  = val<:0 
    ⟦coe cap ⟧  = coerce proj₁  
    ⟦coe crcn ⟧ = coerce proj₁  
    ⟦coe c∘ c12 c23 ⟧ = coerce (ggetfunc c23 ∘ ggetfunc c12)   
  
    ggetfunc : ∀{cn1 cn2} → cn1 <: cn2 → ⟦cn cn1 ⟧ → ⟦cn cn2 ⟧
    ggetfunc cnm = getfunc val<:0
    ggetfunc cap = proj₁
    ggetfunc crcn = proj₁
    ggetfunc (c∘ c12 c23) = ggetfunc c23 ∘ ggetfunc c12
  
    -- AP = (e → t) 
    ⟦ap_⟧ : {cn : CN} → AP cn → (⟦cn cn ⟧ → Set)
    ⟦ap ap-a n ⟧ = valAdj n
  
    -- NP = (e → t) → t
    ⟦np_⟧ : {cn1 : CN} → NP cn1 → {cn2 : CN} → {{⟦cn cn1 ⟧ ⊆ ⟦cn cn2 ⟧}}
          → (⟦cn cn2 ⟧ → Set) → Set  
    ⟦np np-pn n ⟧           ⟦vp⟧ = ⟦vp⟧ ⟪ valPN n ⟫
    ⟦np np-det d cn ⟧ {cn2} ⟦vp⟧ = ⟦det d ⟧ cn {cn2} ⟦vp⟧
    
    -- VP = e → t
    ⟦vp_⟧ : {cn1 : CN} → VP cn1 → {cn2 : CN} → {{⟦cn cn2 ⟧ ⊆ ⟦cn cn1 ⟧}}
          → ⟦cn cn2 ⟧ → Set
    ⟦vp vp-vi n ⟧ x = valVI n ⟪ x ⟫
    ⟦vp vp-vt vt {cn2} np {{coe}} ⟧ x =
      ⟦np np ⟧ {cn2} λ y → valVT vt ⟪ x ⟫ $ ⟪ y ⟫ {{⟦coe coe ⟧}} -- λx.(NP (λy.(VT y x)))
  
    -- Det = (e → t) → ((e → t) → t) 
    ⟦det_⟧ : Det → (cn : CN) → {cn1 : CN} → {{⟦cn cn ⟧ ⊆ ⟦cn cn1 ⟧}}
           → (⟦cn cn1 ⟧ → Set) → Set 
    ⟦det a/an ⟧  cn ⟦vp⟧ = Σ ⟦cn cn ⟧ ⟪→ ⟦vp⟧ ⟫ 
    ⟦det every ⟧ cn ⟦vp⟧ = (x : ⟦cn cn ⟧) → ⟦vp⟧ ⟪ x ⟫
    ⟦det no ⟧    cn ⟦vp⟧ = (x : ⟦cn cn ⟧) → ¬ ⟦vp⟧ ⟪ x ⟫ 
    ⟦det the ⟧   cn ⟦vp⟧ = Σ[ Aₚ ∈ Pointed ⟦cn cn ⟧ ] ⟦vp⟧ ⟪ theₚ Aₚ ⟫
    ⟦det ∅ ⟧     cn ⟦vp⟧ = Σ ⟦cn cn ⟧ ⟪→ ⟦vp⟧ ⟫ 
    
    ⟦s_⟧ : S → Set
    ⟦s s-nv {cn1} np {cn2} vp {{coe}} ⟧ =
      ⟦np np ⟧ {cn1} (⟪→ ⟦vp vp ⟧ {cn2} ⟫ {{⟦coe coe ⟧}})


-- ==================================================================
-- Example1
-- ========

module Ex1 where

  -- Name structure
  
  data nameCN  : Set where Human Dog Animate Object : nameCN
  data namePN  : Set where Alex Mary Polkan : namePN
  data nameVI  : Set where run : nameVI
  data nameVT  : Set where love : nameVT
  data nameAdj : Set where big small : nameAdj
  
  argPN : namePN → nameCN
  argPN Alex = Human
  argPN Mary = Human
  argPN Polkan = Dog
  
  argVI : nameVI → nameCN
  argVI run = Animate
  
  argVT : nameVT → nameCN × nameCN
  argVT love = Animate , Object 
  
  argAdj : nameAdj → nameCN
  argAdj big   = Object
  argAdj small = Object
  
  
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
  <-trans a<o ()
  <-trans h<a a<o = h<o
  <-trans h<o ()
  <-trans d<h h<a = d<a
  <-trans d<h h<o = d<o
  <-trans d<a a<o = d<o
  <-trans d<o ()
  
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
    instance sub1  : ∀{fs1 fs2 f} → {{fs1 ⊆ᶠ fs2}} → fs1 ⊆ᶠ (f ∷ fs2)  
    instance sub2  : ∀{fs1 fs2 f} → {{fs1 ⊆ᶠ fs2}} → (f ∷ fs1) ⊆ᶠ (f ∷ fs2)  
  
  -- some properties
  
  []-⊆ᶠ-f : ∀{fs} → [] ⊆ᶠ fs
  []-⊆ᶠ-f {[]} = sub∅
  []-⊆ᶠ-f {x ∷ fs} = sub1 {_} {fs} {{[]-⊆ᶠ-f {fs}}}
  
  f-⊆ᶠ-f : ∀{fs} → fs ⊆ᶠ fs
  f-⊆ᶠ-f {[]} = sub∅
  f-⊆ᶠ-f {x ∷ fs} = sub2 {{f-⊆ᶠ-f}} 
  
  sub1ʳ : ∀{fs1 fs2 f1} → (f1 ∷ fs1) ⊆ᶠ fs2 → fs1 ⊆ᶠ fs2
  sub1ʳ {[]} {_ ∷ _} _ = []-⊆ᶠ-f
  sub1ʳ (sub1 {{p}}) = sub1 {{sub1ʳ p}}
  sub1ʳ sub2 = sub1
  
  -- Can I prove this?
  -- This seems to hold only for ordered fs!
  -- ⊆ᶠ-to-≡  : ∀{fs1 fs2} → fs1 ⊆ᶠ fs2 → fs2 ⊆ᶠ fs1 → fs1 ≡ fs2
  -- ⊆ᶠ-to-≡ sub∅ sub∅ = refl
  -- ⊆ᶠ-to-≡ {f1 ∷ fs1} {f2 ∷ fs2} (sub1 {{x}}) (sub1 {{y}})
  --     = cong₂ _∷_ (ppp x y) (⊆ᶠ-to-≡ (sub1ʳ x) (sub1ʳ y))
  --   where
  --   ppp : ∀{fs1 fs2 f1 f2} → (f1 ∷ fs1) ⊆ᶠ fs2 → (f2 ∷ fs2) ⊆ᶠ fs1 → f1 ≡ f2
  --   ppp {x ∷ fs1} {y ∷ fs2} {f1} {f2} (sub1 {{p}}) (sub1 {{q}}) = ppp {!sub1!} q
  --   ppp {x ∷ fs1} {y ∷ fs2} {f1} {.x} (sub1 {{p}}) (sub2 {{q}}) = {!!}
  --   ppp {x ∷ fs1} {y ∷ fs2} {.y} {f2} (sub2 {{p}}) (sub1 {{q}}) = {!!}
  --   ppp {x ∷ fs1} {y ∷ fs2} {.y} {.x} (sub2 {{p}}) (sub2 {{q}}) = ppp q p
  -- ⊆ᶠ-to-≡ (sub1 {{x}}) (sub2 {{y}}) = cong₂ _∷_ refl (⊆ᶠ-to-≡ (sub1ʳ x) y)
  -- ⊆ᶠ-to-≡ (sub2 {{x}}) (sub1 {{y}}) = cong₂ _∷_ refl (⊆ᶠ-to-≡ x (sub1ʳ y))
  -- ⊆ᶠ-to-≡ (sub2 {{x}}) (sub2 {{y}}) = cong₂ _∷_ refl (⊆ᶠ-to-≡ x y)
  
  
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
  n1 <:0 n2 = FSet n2 ⊆ᶠ FSet n1
  
  -- Tests
  
  _ : Human <:0 Animate
  _ = it --sub2 
  
  _ : Dog <:0 Object
  _ = it --sub2 
  
  _ : Dog <:0 Dog
  _ = it --f-⊆ᶠ-f 
  
  
  NS : NameStructure
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
    ⦅_⦆  : ∀ {f1 f2} → {{f2 ⊆ᶠ f1}} → ⟦CN⟧ f1 → ⟦CN⟧ f2 -- with features f2 and more
  
  -- the same ⟦CN⟧ fs for the same fs
  uniq-⟦CN⟧ : ∀{fs1 fs2} → fs1 ≡ fs2 → ⟦CN⟧ fs1 ≡ ⟦CN⟧ fs2
  uniq-⟦CN⟧ refl = refl
  
  -- cannot be proven in general!
  -- uniq' : ∀{fs1 fs2} → ⟦CN⟧ fs1 ≡ ⟦CN⟧ fs2 → fs1 ≡ fs2 
  
  
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
    *big    : *Object → Set
    *small  : *Object → Set 
  
  ⦅→_⦆ : ∀{fs1 fs2} → (⟦CN⟧ fs1 → Set) → {{fs1 ⊆ᶠ fs2}} → (⟦CN⟧ fs2 → Set)
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
  valAdj big   = *big
  valAdj small = *small
  
  val<:0 : ∀{n1 n2} → {{n1 <:0 n2}} → valCN n1 ⊆ valCN n2
  val<:0 = coerce ⦅_⦆
  
  M : Model NS
  M = record { valCN  = valCN
             ; valPN  = valPN
             ; valVI  = valVI
             ; valVT  = valVT
             ; valAdj = valAdj
             ; val<:0 = λ {n1} {n2} → val<:0 {n1} {n2}
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
    *polkan-is-big : *big ⦅ *Polkan ⦆
    *polkan-runs : ⦅ *Polkan ⦆ *run
  
  big-dog = cn-ap (ap-a big) (cn-n Dog)
  
  *big-dog : ⟦cn big-dog ⟧
  *big-dog = *Polkan , *polkan-is-big 

  -- a big dog runs
  s8 = s-nv (np-det a/an big-dog) (vp-vi run) {{c∘ cap it}}

  _ : ⟦s s8 ⟧ ≡ (Σ[ bd ∈ (Σ[ b ∈ *Dog ] *big ⦅ b ⦆) ] ⦅ proj₁ bd ⦆ *run)
  _ = refl

  _ : ⟦s s8 ⟧
  _ = (*Polkan , *polkan-is-big) , *polkan-runs

  
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
                                 {{c∘ ((c∘ {cn3 = (cn-n Animate)} crcn it)) it}}
                                 -- {{c∘ ((c∘ crcn (Syntax.cnm {n2 = Animate}))) Syntax.cnm}}
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
    instance sub1 : ∀{fs1 fs2 f} → {{fs1 ⊆ᶠ fs2}} → fs1 ⊆ᶠ (f ∷ fs2)  
    instance sub2 : ∀{fs1 fs2 f} → {{fs1 ⊆ᶠ fs2}} → (f ∷ fs1) ⊆ᶠ (f ∷ fs2)  
  
  -- some properties
  
  []-⊆ᶠ-f : ∀{fs} → [] ⊆ᶠ fs
  []-⊆ᶠ-f {[]} = sub∅
  []-⊆ᶠ-f {x ∷ fs} = sub1 {_} {fs} {{[]-⊆ᶠ-f {fs}}}
  
  f-⊆ᶠ-f : ∀{fs} → fs ⊆ᶠ fs
  f-⊆ᶠ-f {[]} = sub∅
  f-⊆ᶠ-f {x ∷ fs} = sub2 {{f-⊆ᶠ-f}} 
  
  sub1ʳ : ∀{fs1 fs2 f1} → (f1 ∷ fs1) ⊆ᶠ fs2 → fs1 ⊆ᶠ fs2
  sub1ʳ {[]} {_ ∷ _} _ = []-⊆ᶠ-f
  sub1ʳ (sub1 {{p}}) = sub1 {{sub1ʳ p}}
  sub1ʳ sub2 = sub1
  
  -- Can I prove this?
  -- This seems to hold only for ordered fs!
  -- ⊆ᶠ-to-≡  : ∀{fs1 fs2} → fs1 ⊆ᶠ fs2 → fs2 ⊆ᶠ fs1 → fs1 ≡ fs2
  -- ⊆ᶠ-to-≡ sub∅ sub∅ = refl
  -- ⊆ᶠ-to-≡ {f1 ∷ fs1} {f2 ∷ fs2} (sub1 {{x}}) (sub1 {{y}})
  --     = cong₂ _∷_ (ppp x y) (⊆ᶠ-to-≡ (sub1ʳ x) (sub1ʳ y))
  --   where
  --   ppp : ∀{fs1 fs2 f1 f2} → (f1 ∷ fs1) ⊆ᶠ fs2 → (f2 ∷ fs2) ⊆ᶠ fs1 → f1 ≡ f2
  --   ppp {x ∷ fs1} {y ∷ fs2} {f1} {f2} (sub1 {{p}}) (sub1 {{q}}) = ppp {!sub1!} q
  --   ppp {x ∷ fs1} {y ∷ fs2} {f1} {.x} (sub1 {{p}}) (sub2 {{q}}) = {!!}
  --   ppp {x ∷ fs1} {y ∷ fs2} {.y} {f2} (sub2 {{p}}) (sub1 {{q}}) = {!!}
  --   ppp {x ∷ fs1} {y ∷ fs2} {.y} {.x} (sub2 {{p}}) (sub2 {{q}}) = ppp q p
  -- ⊆ᶠ-to-≡ (sub1 {{x}}) (sub2 {{y}}) = cong₂ _∷_ refl (⊆ᶠ-to-≡ (sub1ʳ x) y)
  -- ⊆ᶠ-to-≡ (sub2 {{x}}) (sub1 {{y}}) = cong₂ _∷_ refl (⊆ᶠ-to-≡ x (sub1ʳ y))
  -- ⊆ᶠ-to-≡ (sub2 {{x}}) (sub2 {{y}}) = cong₂ _∷_ refl (⊆ᶠ-to-≡ x y)
  
  
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
  n1 <:0 n2 = FSet n2 ⊆ᶠ FSet n1
  
  -- Tests
  
  _ : Book <:0 Info
  _ = sub1 
  
  _ : Book <:0 Phys
  _ = sub2
  
  _ : Info <:0 Info
  _ = f-⊆ᶠ-f 
  
  
  NS : NameStructure
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
    ⦅_⦆  : ∀ {f1 f2} → {{f2 ⊆ᶠ f1}} → ⟦CN⟧ f1 → ⟦CN⟧ f2 
  
  -- the same ⟦CN⟧ fs for the same fs
  uniq-⟦CN⟧ : ∀{fs1 fs2} → fs1 ≡ fs2 → ⟦CN⟧ fs1 ≡ ⟦CN⟧ fs2
  uniq-⟦CN⟧ refl = refl
  
  -- cannot be proven in general!
  -- uniq' : ∀{fs1 fs2} → ⟦CN⟧ fs1 ≡ ⟦CN⟧ fs2 → fs1 ≡ fs2 
  
  
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
  
  val<:0 : ∀{n1 n2} → {{n1 <:0 n2}} → valCN n1 ⊆ valCN n2
  val<:0 = coerce ⦅_⦆
  
  M : Model NS
  M = record { valCN  = valCN
             ; valPN  = valPN
             ; valVI  = valVI
             ; valVT  = valVT
             ; valAdj = valAdj
             ; val<:0 = λ {n1} {n2} → val<:0 {n1} {n2}
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
  
  
