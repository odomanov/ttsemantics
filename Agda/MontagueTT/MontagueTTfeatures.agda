-- Montague-like type-theoretical semantics.
-- With coercion through features.

module _ where

open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.List
open import Data.Product
open import Function
open import Relation.Nullary renaming (no to not)
open import Relation.Binary.PropositionalEquality
open import Level renaming (zero to lzero; suc to lsuc)

open import Relation.Binary
open import Relation.Binary.Definitions

-- open import EqReflection2


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


-- Definitions for features
-- ========================

record Eq (A : Set) : Set where
  field
    _==_ : A → A → Bool

open Eq {{...}} public

_==ˡ_ : {A : Set} → {{Eq A}} → List A → List A → Bool
[] ==ˡ [] = true
(x ∷ xs) ==ˡ (y ∷ ys) = x == y ∧ xs ==ˡ ys
_ ==ˡ _ = false

module FeatureStructure (Feature : Set)
                        {{eq : Eq Feature}}
                        (_<_ : Feature → Feature → Set)
                        (isSTO : IsStrictTotalOrder _≡_ _<_)
                        where

  open IsStrictTotalOrder isSTO public
  
  FS = List Feature       -- feature sets
  
  empty : FS
  empty = []
  
  -- insert guarantees 1) order, 2) uniqueness
  insert : Feature → FS → FS
  insert x [] = x ∷ []
  insert x (f ∷ fs) with compare x f
  ... | tri< a ¬b ¬c = f ∷ insert x fs
  ... | tri≈ ¬a b ¬c = f ∷ fs
  ... | tri> ¬a ¬b c = x ∷ f ∷ fs
  
  -- also guarantees order and uniqueness
  {-# TERMINATING #-}
  intersection : FS → FS → FS
  intersection [] _ = []
  intersection _ [] = []
  intersection (x ∷ xs) (y ∷ ys) with compare x y
  ... | tri< _ _ _ = intersection (x ∷ xs) ys
  ... | tri≈ _ _ _ = x ∷ intersection xs ys
  ... | tri> _ _ _ = intersection xs (y ∷ ys)
  
  -- since refl is instance, ⊆ᶠ is also instance
  _⊆ᶠ_ : FS → FS → Set
  f1 ⊆ᶠ f2 = intersection f1 f2 ≡ f1
  

-- The structure to hold names
-- ===========================

record NameStructure : Set₁ where
  field
    nameCN namePN nameVI nameVT nameAdj : Set  -- names for syntactic categories
    -- eqCN   : (x y : nameCN)  → Dec (x ≡ y)   
    -- eqPN   : (x y : namePN)  → Dec (x ≡ y)
    -- eqVI   : (x y : nameVI)  → Dec (x ≡ y)
    -- eqVT   : (x y : nameVT)  → Dec (x ≡ y)
    -- eqAdj  : (x y : nameAdj) → Dec (x ≡ y)
    argPN  : namePN  → nameCN                   -- argument types etc.
    argVI  : nameVI  → nameCN
    argVT  : nameVT  → nameCN × nameCN
    argAdj : nameAdj → nameCN
    _<:0_  : nameCN → nameCN → Set       -- coercion on the syntax level


-- Синтаксис
-- =========

module Syntax (nam : NameStructure) where

  open NameStructure nam 
  
  mutual
  
    data CN : Set where
      use-cn : nameCN → CN
      cn-ap  : {cn1 : CN} → AP cn1 → (cn2 : CN) → {{cn2 <: cn1}} → CN
      rcn    : (cn1 : CN) {cn2 : CN} → VP cn2 → {{cn1 <: cn2}} → CN    -- CN that VP
      
    data _<:_ : CN → CN → Set where
      instance
        ccc  : ∀ {cn} → cn <: cn
        cap  : ∀ {cn1 cn2 ap coe} → cn-ap {cn1} ap cn2 {{coe}} <: cn2
        crcn : ∀ {cn1 cn2 vp coe} → rcn cn1 {cn2} vp {{coe}} <: cn1
        cnm  : ∀ {n1 n2} → {{n1 <:0 n2}} → use-cn n1 <: use-cn n2
      c∘   : ∀ {cn1 cn2 cn3} → cn1 <: cn2 → cn2 <: cn3 → cn1 <: cn3

    data VI : CN → Set where
      use-vi : (n : nameVI) → VI $ use-cn $ argVI n
  
    -- порядок аргументов в VT прямой!  VT A B => A → B → Set
    data VT : CN → CN → Set where
      use-vt : (n : nameVT) → VT (use-cn (proj₁ (argVT n)))
                                 (use-cn (proj₂ (argVT n)))
      
    data PN : CN → Set where
      use-pn : (n : namePN) → PN $ use-cn $ argPN n
    
    data Adj : CN → Set where
      use-adj : (n : nameAdj) → Adj $ use-cn $ argAdj n
      
    data DET : Set where
      a/an every no the ∅ : DET
  
    data VP (cn : CN) : Set where
      vp-vi : VI cn → VP cn
      vp-vt : {cn1 : CN} → VT cn cn1 → {cn2 : CN} → NP cn2
            → {{coe : cn2 <: cn1}} → VP cn
    
    data NP : (cn : CN) → Set where
      np-pn  : ∀{cn} → PN cn → NP cn
      np-det : DET → (cn : CN) → NP cn
    
    data AP (cn : CN) : Set where
      ap-a : Adj cn → AP cn
      -- ap-a   : ∀ {cn1 cn2} → AP cn1 → AP cn2 → AP cn2
      
    data S : Set where
      s-nv  : ∀{cn1} → NP cn1 → ∀{cn2} → VP cn2 → {{coe : cn1 <: cn2}} → S
      -- s-nvn : ∀ {cn1 cn2} → NP cn1 → VT cn1 cn2 → NP cn2 → S


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
  open Pointed    
  
  mutual
  
    -- CN ≠ e → t !  CN это тип.
    ⟦cn_⟧ : CN → Set
    ⟦cn use-cn n ⟧ = valCN n
    ⟦cn cn-ap ap cn {{coe}} ⟧ = ⟪Σ⟫ ⟦cn cn ⟧ ⟦ap ap ⟧ {{⟦coe coe ⟧}}  
    ⟦cn rcn cn1 {cn2} vp {{coe}} ⟧ = ⟪Σ⟫ ⟦cn cn1 ⟧ (⟦vp vp ⟧ {cn2}) {{⟦coe coe ⟧}} 
  
    ⟦coe_⟧ : {cn1 cn2 : CN} → (cn1 <: cn2) → (⟦cn cn1 ⟧ ⊆ ⟦cn cn2 ⟧)
    ⟦coe ccc ⟧  = Idc 
    ⟦coe cnm ⟧  = val<:0 
    ⟦coe cap ⟧  = Prc 
    ⟦coe crcn ⟧ = Prc 
    ⟦coe c∘ c12 c23 ⟧ = coerce (ggetfunc c23 ∘ ggetfunc c12)   
  
    ggetfunc : ∀{cn1 cn2} → cn1 <: cn2 → ⟦cn cn1 ⟧ → ⟦cn cn2 ⟧
    ggetfunc ccc = id
    ggetfunc cnm = getfunc val<:0
    ggetfunc cap = proj₁
    ggetfunc crcn = proj₁
    ggetfunc (c∘ c12 c23) = ggetfunc c23 ∘ ggetfunc c12
  
    ⟦pn_⟧ : {cn : CN} → PN cn → ⟦cn cn ⟧
    ⟦pn use-pn n ⟧   = valPN n 
    
    -- VI = e → t
    ⟦vi_⟧ : {cn : CN} → VI cn → ⟦cn cn ⟧ → Set
    ⟦vi use-vi n ⟧ = valVI n
  
    -- VT = e → e → t
    ⟦vt_⟧ : ∀ {cn1 cn2} → VT cn1 cn2 → ⟦cn cn1 ⟧ → ⟦cn cn2 ⟧ → Set
    ⟦vt use-vt n ⟧ = valVT n
  
    -- AP = (e → t) 
    ⟦ap_⟧ : {cn : CN} → AP cn → (⟦cn cn ⟧ → Set)
    ⟦ap ap-a (use-adj n) ⟧ = valAdj n
  
    -- NP = (e → t) → t
    ⟦np_⟧ : {cn1 : CN} → NP cn1 → {cn2 : CN} → {{⟦cn cn1 ⟧ ⊆ ⟦cn cn2 ⟧}}
          → (⟦cn cn2 ⟧ → Set) → Set  
    ⟦np np-pn pn ⟧          ⟦vp⟧ = ⟦vp⟧ ⟪ ⟦pn pn ⟧ ⟫
    ⟦np np-det d cn ⟧ {cn2} ⟦vp⟧ = ⟦det d ⟧ cn {cn2} ⟦vp⟧
    
    -- VP = e → t
    ⟦vp_⟧ : {cn1 : CN} → VP cn1 → {cn2 : CN} → {{⟦cn cn2 ⟧ ⊆ ⟦cn cn1 ⟧}}
          → ⟦cn cn2 ⟧ → Set
    ⟦vp vp-vi vi ⟧ x = ⟦vi vi ⟧ ⟪ x ⟫
    ⟦vp vp-vt {cn1} vt {cn2} np {{coe}} ⟧ x =
      ⟦np np ⟧ {cn2} λ y → ⟦vt vt ⟧ ⟪ x ⟫ (⟪ y ⟫ {{⟦coe coe ⟧}}) -- λx.(NP (λy.(VT y x)))
  
    -- DET = (e → t) → ((e → t) → t) 
    ⟦det_⟧ : DET → (cn : CN) → {cn1 : CN} → {{⟦cn cn ⟧ ⊆ ⟦cn cn1 ⟧}}
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
-- Example
-- =======

-- Name structure

data nameCN  : Set where Human Dog Animate Object : nameCN
data namePN  : Set where Alex Mary Polkan : namePN
data nameVI  : Set where runs : nameVI
data nameVT  : Set where love : nameVT
data nameAdj : Set where big small : nameAdj

argPN : namePN → nameCN
argPN Alex = Human
argPN Mary = Human
argPN Polkan = Dog

argVI : nameVI → nameCN
argVI runs = Animate

argVT : nameVT → nameCN × nameCN
argVT love = Animate , Object 

argAdj : nameAdj → nameCN
argAdj big   = Object
argAdj small = Object

-- eqCN : (x y : nameCN) → Dec (x ≡ y)
-- unquoteDef eqCN = ddef (quote nameCN) eqCN 

-- eqPN : (x y : namePN) → Dec (x ≡ y)
-- unquoteDef eqPN = ddef (quote namePN) eqPN 

-- eqVI : (x y : nameVI) → Dec (x ≡ y)
-- eqVI runs runs = yes refl

-- eqVT : (x y : nameVT) → Dec (x ≡ y)
-- eqVT love love = yes refl

-- eqAdj : (x y : nameAdj) → Dec (x ≡ y)
-- unquoteDef eqAdj = ddef (quote nameAdj) eqAdj 



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

instance
  eqF : Eq Feature
  _==_ ⦃ eqF ⦄ f-animate f-animate = true
  _==_ ⦃ eqF ⦄ f-dog f-dog = true
  _==_ ⦃ eqF ⦄ f-human f-human = true
  _==_ ⦃ eqF ⦄ f-object f-object = true
  _==_ ⦃ eqF ⦄ _ _ = false

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

open FeatureStructure Feature _<_ isSTO

-- feature sets for types

FO : FS
FO = insert f-object empty

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


_ : empty ⊆ᶠ empty 
_ = refl

_ : empty ⊆ᶠ FH
_ = refl

_ : FO ⊆ᶠ FA
_ = refl

_ : FO ⊆ᶠ FH
_ = refl

_ : FO ⊆ᶠ FO
_ = refl

_ : FA ⊆ᶠ FD
_ = refl

_ : FA ⊆ᶠ FH
_ = refl

int[] : ∀{fs} → intersection fs [] ≡ []
int[] {[]} = refl
int[] {x ∷ fs} = refl

cff : ∀{fs} → fs ⊆ᶠ fs
cff {[]} = refl
cff {x ∷ xs} with compare x x
... | tri≈ _ refl _ = f refl cff
  where
  f : ∀{x y : Feature}→ ∀{xs ys} → x ≡ y → (xs ≡ ys) → x ∷ xs ≡ y ∷ ys
  f refl refl = refl


-- Connect names and feature sets

FSet : nameCN → FS
FSet Human   = FH
FSet Dog     = FD
FSet Animate = FA
FSet Object  = FO

-- Syntac level coercion for basic types/names
_<:0_ : nameCN → nameCN → Set
n1 <:0 n2 = FSet n2 ⊆ᶠ FSet n1

-- Tests

_ : Human <:0 Animate
_ = refl

_ : Dog <:0 Object
_ = refl

_ : Dog <:0 Dog
_ = refl


NS : NameStructure
NS = record { nameCN = nameCN; namePN = namePN; nameVI = nameVI
            ; nameVT = nameVT; nameAdj = nameAdj
            -- ; eqCN = eqCN; eqPN = eqPN; eqVI = eqVI; eqVT = eqVT; eqAdj = eqAdj
            ; argPN = argPN; argVI = argVI; argVT = argVT; argAdj = argAdj
            ; _<:0_ = _<:0_
            }



-- Семантика
-- =========

-- The type of objects having features FS
data ⟦CN⟧ : FS → Set where
  base : (n : namePN) → ⟦CN⟧ (FSet (argPN n))
  《_》  : ∀ {f1 f2} → {{f2 ⊆ᶠ f1}} → ⟦CN⟧ f1 → ⟦CN⟧ f2 -- with features f2 and more

-- Aliases

*Human   = ⟦CN⟧ FH
*Dog     = ⟦CN⟧ FD
*Animate = ⟦CN⟧ FA
*Object  = ⟦CN⟧ FO

*Alex   = base Alex
*Mary   = base Mary
*Polkan = base Polkan


-- Tests

_ : *Human
_ = 《 *Mary 》

_ : *Animate
_ = 《 *Mary 》

_ : *Object
_ = 《 *Mary 》

_ : *Object
_ = 《 *Polkan 》

postulate
  _*runs  : *Animate → Set
  _*love_ : *Animate → *Object → Set
  *big    : *Object → Set
  *small  : *Object → Set 

-- 《→_》 : ∀{fs1 fs2} → (⟦CN⟧ fs1 → Set) → {{fs1 ⊆ᶠ fs2}} → (⟦CN⟧ fs2 → Set)
-- 《→ f 》 x = f 《 x 》

-- _ : *Human → Set
-- _ = λ x → 《 x 》 *runs

-- _ : *Dog → Set
-- _ = 《→ _*runs 》 


-- Names valuation

valCN : nameCN → Set
valCN n = ⟦CN⟧ (FSet n)

valPN  : (n : namePN)  → valCN (argPN n)
valPN n = base n

valVI  : (n : nameVI)  → valCN (argVI n) → Set
valVI runs = _*runs

valVT  : (n : nameVT)  → valCN (proj₁ (argVT n)) → valCN (proj₂ (argVT n)) → Set
valVT love = _*love_

valAdj : (n : nameAdj) → valCN (argAdj n) → Set
valAdj big = *big
valAdj small = *small

val<:0 : ∀{n1 n2} → {{n1 <:0 n2}} → valCN n1 ⊆ valCN n2
val<:0 = coerce 《_》

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


s1 = s-nv (np-pn (use-pn Mary)) (vp-vi (use-vi runs)) 

_ : ⟦s s1 ⟧ ≡  《 *Mary 》 *runs
_ = refl


s3 = s-nv (np-pn (use-pn Polkan)) (vp-vi (use-vi runs))      -- coercion working


-- a human runs
s4 = s-nv (np-det a/an (use-cn Human)) (vp-vi (use-vi runs)) 

-- _ : ⟦s s4 ⟧ ≡ ⟪Σ⟫ *Human 《→ _*runs 》 
-- _ = refl

_ : ⟦s s4 ⟧ ≡ Σ *Human (λ x → 《 x 》 *runs)             --⟪Σ⟫ *Human _*runs 
_ = refl

-- _ : ⟦s s4 ⟧ ≡ Σ *Human 《→ _*runs 》    
-- _ = refl


-- every human runs
s5 = s-nv (np-det every (use-cn Human)) (vp-vi (use-vi runs))

_ : ⟦s s5 ⟧ ≡ ((x : *Human) → 《 x 》 *runs)
_ = refl


-- the human runs
s6 = s-nv (np-det the (use-cn Human)) (vp-vi (use-vi runs))

_ : ⟦s s6 ⟧
_ = Hₚ , *Mary-runs
  where
  Hₚ : Pointed *Human 
  Hₚ = record { theₚ = *Mary }

  postulate *Mary-runs : 《 *Mary 》 *runs


-- Прилагательные / свойства

postulate
  *polkan-is-big : *big 《 *Polkan 》

big-dog : ⟦cn cn-ap (ap-a (use-adj big)) (use-cn Dog) ⟧ 
big-dog = *Polkan , *polkan-is-big 


-- Относительные конструкции (CN that VP и пр.)

human-that-runs : CN
human-that-runs = rcn (use-cn Human) (vp-vi (use-vi runs))

_ : ⟦cn human-that-runs ⟧
_ = *Mary , *Mary-runs
  where postulate *Mary-runs : 《 *Mary 》 *runs 


a-human-that-runs : NP _ 
a-human-that-runs = np-det a/an human-that-runs

-- a human that runs runs
s9 = s-nv a-human-that-runs (vp-vi (use-vi runs)) {{c∘ crcn Syntax.cnm}}   -- работает! 


-- Mary loves Alex

loves-Alex : VP _
loves-Alex = vp-vt (use-vt love) (np-pn (use-pn Alex))

s11 = s-nv (np-pn (use-pn Mary)) loves-Alex

_ : ⟦s s11 ⟧ ≡ 《 *Mary 》 *love 《 *Alex 》
_ = refl


-- Mary loves Polkan

s12 = s-nv (np-pn (use-pn Mary)) (vp-vt (use-vt love) (np-pn (use-pn Polkan)))

_ : ⟦s s12 ⟧ ≡ 《 *Mary 》 *love 《 *Polkan 》 
_ = refl


-- Mary loves a human that runs

s13 = s-nv (np-pn (use-pn Mary)) (vp-vt (use-vt love) a-human-that-runs 
                                        {{c∘ ((c∘ crcn (Syntax.cnm {n2 = Animate}))) Syntax.cnm}}
                                        )

_ : ⟦s s13 ⟧ ≡ (Σ[ hruns ∈ Σ[ h ∈ *Human ] 《 h 》 *runs ] 《 *Mary 》 *love 《 《 proj₁ hruns 》 》)
_ = refl

