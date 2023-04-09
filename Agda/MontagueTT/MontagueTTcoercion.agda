{-# OPTIONS --overlapping-instances #-}
-- Montague semantics in terms of TT.
-- With coercion.

module _ where

open import Data.Product
open import Function
open import Relation.Nullary renaming (no to not)
open import Relation.Binary.PropositionalEquality
open import Coercion renaming (_<:_ to _⟦<:⟧_)

instance
  Idc : ∀ {ℓ} {A : Set ℓ} → A ⟦<:⟧ A
  Idc = coerce id 
  Prc : ∀{a b} → {A : Set a} → {B : A → Set b} → Σ A B ⟦<:⟧ A
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

record Model (nam : LexStructure) : Set₁ where
  open LexStructure nam 
  field
    valCN  : nameCN → Set
    valPN  : (n : namePN)  → valCN (argPN n) 
    valVI  : (n : nameVI)  → valCN (argVI n) → Set
    valVT  : (n : nameVT)  → valCN (proj₁ (argVT n))
                           → valCN (proj₂ (argVT n)) → Set
    valAdj : (n : nameAdj) → valCN (argAdj n) → Set
    val<:0 : ∀{n1 n2} → {{n1 <:0 n2}} → valCN n1 ⟦<:⟧ valCN n2


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
    ⟦cn rcn cn1 {cn2} vp {{coe}} ⟧ = ⟪Σ⟫ ⟦cn cn1 ⟧ (⟦vp vp ⟧ {cn2}) {{⟦coe coe ⟧}} 
  
    ⟦coe_⟧ : {cn1 cn2 : CN} → (cn1 <: cn2) → (⟦cn cn1 ⟧ ⟦<:⟧ ⟦cn cn2 ⟧)
    ⟦coe cnm ⟧  = val<:0 
    ⟦coe cap ⟧  = coerce proj₁  
    ⟦coe crcn ⟧ = coerce proj₁  
    ⟦coe c∘ c12 c23 ⟧ = ⟦coe c23 ⟧ ⟪∘⟫ ⟦coe c12 ⟧ 
  
    -- AP = (e → t) 
    ⟦ap_⟧ : {cn : CN} → AP cn → (⟦cn cn ⟧ → Set)
    ⟦ap ap-a n ⟧ = valAdj n
  
    -- NP = (e → t) → t
    ⟦np_⟧ : {cn1 : CN} → NP cn1 → {cn2 : CN} → {{⟦cn cn1 ⟧ ⟦<:⟧ ⟦cn cn2 ⟧}}
          → (⟦cn cn2 ⟧ → Set) → Set  
    ⟦np np-pn n ⟧           ⟦vp⟧ = ⟦vp⟧ ⟪ valPN n ⟫
    ⟦np np-det d cn ⟧ {cn2} ⟦vp⟧ = ⟦det d ⟧ cn {cn2} ⟦vp⟧
    
    -- VP = e → t
    ⟦vp_⟧ : {cn1 : CN} → VP cn1 → {cn2 : CN} → {{⟦cn cn2 ⟧ ⟦<:⟧ ⟦cn cn1 ⟧}}
          → ⟦cn cn2 ⟧ → Set
    ⟦vp vp-vi n ⟧ x = valVI n ⟪ x ⟫
    ⟦vp vp-vt vt {cn2} np {{coe}} ⟧ x =
      ⟦np np ⟧ {cn2} λ y → valVT vt ⟪ x ⟫ $ ⟪ y ⟫ {{⟦coe coe ⟧}} -- λx.(NP (λy.(VT y x)))
  
    -- Det = (e → t) → ((e → t) → t) 
    ⟦det_⟧ : Det → (cn : CN) → {cn1 : CN} → {{⟦cn cn ⟧ ⟦<:⟧ ⟦cn cn1 ⟧}}
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
  
  -- Syntax level coercion for basic types/names
  data _<:0_ : nameCN → nameCN → Set where
    instance
      cha : Human <:0 Animate
      cda : Dog <:0 Animate
      cao : Animate <:0 Object
      cho : Human <:0 Object
      cdo : Dog <:0 Object
      ccc : ∀{A} → A <:0 A
    
  NS : LexStructure
  NS = record { nameCN = nameCN; namePN = namePN; nameVI = nameVI
              ; nameVT = nameVT; nameAdj = nameAdj
              ; argPN = argPN; argVI = argVI; argVT = argVT; argAdj = argAdj
              ; _<:0_ = _<:0_
              }
  
  postulate
    *Human *Dog *Animate *Object : Set
    *Alex *Mary : *Human
    *Polkan     : *Dog
    _*run       : *Animate → Set
    _*love_     : *Animate → *Object → Set
    *black      : *Object → Set
  
  postulate
    fDA : *Dog → *Animate
    fHA : *Human → *Animate
    fAO : *Animate → *Object
    
  instance
    HAc : *Human ⟦<:⟧ *Animate
    HAc = coerce fHA
    DAc : *Dog ⟦<:⟧ *Animate
    DAc = coerce fDA
    AOc : *Animate ⟦<:⟧ *Object
    AOc = coerce fAO
    HOc : *Human ⟦<:⟧ *Object
    HOc = AOc ⟪∘⟫ HAc           --coerce (fAO ∘ fHA)
    DOc : *Dog ⟦<:⟧ *Object
    DOc = AOc ⟪∘⟫ DAc           --coerce (fAO ∘ fDA)
    

  -- Names valuation
  
  valCN : nameCN → Set
  valCN Human   = *Human
  valCN Dog     = *Dog
  valCN Animate = *Animate
  valCN Object  = *Object
  
  valPN  : (n : namePN)  → valCN (argPN n)
  valPN Alex   = *Alex
  valPN Mary   = *Mary
  valPN Polkan = *Polkan
  
  valVI  : (n : nameVI)  → valCN (argVI n) → Set
  valVI run = _*run
  
  valVT  : (n : nameVT)  → valCN (proj₁ (argVT n)) → valCN (proj₂ (argVT n)) → Set
  valVT love = _*love_
  
  valAdj : (n : nameAdj) → valCN (argAdj n) → Set
  valAdj black = *black
  
  val<:0 : ∀{n1 n2} → {{n1 <:0 n2}} → valCN n1 ⟦<:⟧ valCN n2
  val<:0 {Human} {Human} = Idc
  val<:0 {Human} {Animate} = HAc
  val<:0 {Human} {Object} = HOc
  val<:0 {Dog} {Dog} = Idc
  val<:0 {Dog} {Animate} = DAc
  val<:0 {Dog} {Object} = DOc
  val<:0 {Animate} {Animate} = Idc
  val<:0 {Animate} {Object} = AOc
  val<:0 {Object} {Object} = Idc
  
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
  
  _ : ⟦s s1 ⟧ ≡  ⟪ *Mary ⟫ *run
  _ = refl
  
  
  s2 = s-nv (np-pn Polkan) (vp-vi run) 
  
  _ : ⟦s s2 ⟧ ≡  ⟪ *Polkan ⟫ *run
  _ = refl
  
  
  -- a human runs
  s3 = s-nv (np-det a/an (cn-n Human)) (vp-vi run) 
  
  _ : ⟦s s3 ⟧ ≡ ⟪Σ⟫ *Human _*run  
  _ = refl
  
  _ : ⟦s s3 ⟧ ≡ Σ *Human (λ x → ⟪ x ⟫ *run)             --⟪Σ⟫ *Human _*run 
  _ = refl
  
  _ : ⟦s s3 ⟧ ≡ Σ *Human ⟪→ _*run ⟫    
  _ = refl
  
  
  -- every human runs
  s4 = s-nv (np-det every (cn-n Human)) (vp-vi run)
  
  _ : ⟦s s4 ⟧ ≡ ((x : *Human) → ⟪ x ⟫ *run)
  _ = refl
  
  
  -- the human runs
  s5 = s-nv (np-det the (cn-n Human)) (vp-vi run)
  
  _ : ⟦s s5 ⟧ ≡ (Σ[ Aₚ ∈ Pointed *Human ] ⟪ theₚ Aₚ ⟫ *run)
  _ = refl
  
  _ : ⟦s s5 ⟧
  _ = Hₚ , *Mary-run
    where
    Hₚ : Pointed *Human 
    Hₚ = record { theₚ = *Mary }
  
    postulate *Mary-run : ⟪ *Mary ⟫ *run
  
  
  -- Mary loves Alex
  
  loves-Alex : VP _
  loves-Alex = vp-vt love (np-pn Alex)
  
  s6 = s-nv (np-pn Mary) loves-Alex
  
  _ : ⟦s s6 ⟧ ≡ ⟪ *Mary ⟫ *love ⟪ *Alex ⟫
  _ = refl
  
  
  -- Mary loves Polkan
  
  s7 = s-nv (np-pn Mary) (vp-vt love (np-pn Polkan))
  
  _ : ⟦s s7 ⟧ ≡ ⟪ *Mary ⟫ *love ⟪ *Polkan ⟫ 
  _ = refl
  
  
  -- Прилагательные / свойства
  
  postulate
    *polkan-is-black : *black ⟪ *Polkan ⟫
    *polkan-runs : ⟪ *Polkan ⟫ *run
  
  black-dog = cn-ap (ap-a black) (cn-n Dog)
  
  *black-dog : ⟦cn black-dog ⟧
  *black-dog = *Polkan , *polkan-is-black 

  -- a black dog runs
  s8 = s-nv (np-det a/an black-dog) (vp-vi run) {{c∘ cap it}}

  _ : ⟦s s8 ⟧ ≡ (Σ[ bd ∈ (Σ[ b ∈ *Dog ] *black ⟪ b ⟫) ] ⟪ proj₁ bd ⟫ *run)
  _ = refl

  _ : ⟦s s8 ⟧
  _ = (*Polkan , *polkan-is-black) , *polkan-runs

  
  -- Относительные конструкции (CN that VP и пр.)
  
  human-that-runs : CN
  human-that-runs = rcn (cn-n Human) (vp-vi run)

  _ : ⟦cn human-that-runs ⟧ ≡ (Σ[ h ∈ *Human ] ⟪ h ⟫ *run)
  _ = refl

  _ : ⟦cn human-that-runs ⟧
  _ = *Mary , *Mary-runs
    where postulate *Mary-runs : ⟪ *Mary ⟫ *run 
  
  
  a-human-that-runs : NP _ 
  a-human-that-runs = np-det a/an human-that-runs

  -- a human that runs runs
  s9 = s-nv a-human-that-runs (vp-vi run) {{c∘ crcn it}} 
  
  
  -- Mary loves a human that runs
  
  s10 = s-nv (np-pn Mary) (vp-vt love a-human-that-runs 
                                 {{c∘ ((c∘ {cn3 = (cn-n Animate)} crcn it)) it}}
                          )
  
  _ : ⟦s s10 ⟧ ≡ (Σ[ hr ∈ Σ[ h ∈ *Human ] ⟪ h ⟫ *run ] ⟪ *Mary ⟫ *love ⟪ ⟪ proj₁ hr ⟫ ⟫ {{HOc}})
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
  

  -- Syntax level coercion for basic types/names
  data _<:0_ : nameCN → nameCN → Set where
    instance
      cbi : Book <:0 Info
      cbp : Book <:0 Phys
      ccc : ∀{A} → A <:0 A
  
  NS : LexStructure
  NS = record { nameCN = nameCN; namePN = namePN; nameVI = nameVI
              ; nameVT = nameVT; nameAdj = nameAdj
              ; argPN = argPN; argVI = argVI; argVT = argVT; argAdj = argAdj
              ; _<:0_ = _<:0_
              }
  
  
  
  -- Семантика
  -- =========
  
  postulate
    *Human *Info *Phys *Book : Set
    *John : *Human
    *War-and-Peace : *Book
    _*take_ : *Human → *Phys → Set
    _*read_ : *Human → *Info → Set
  
  
  postulate
    fBI : *Book → *Info
    fBP : *Book → *Phys
    
  instance
    BIc : *Book ⟦<:⟧ *Info
    BIc = coerce fBI
    BPc : *Book ⟦<:⟧ *Phys
    BPc = coerce fBP
    
  -- Valuation for names
  
  valCN : nameCN → Set
  valCN Human = *Human
  valCN Info = *Info
  valCN Phys = *Phys
  valCN Book = *Book
  
  valPN  : (n : namePN)  → valCN (argPN n)
  valPN John = *John
  valPN War-and-Peace = *War-and-Peace
  
  valVI  : (n : nameVI)  → valCN (argVI n) → Set
  valVI ()
  
  valVT  : (n : nameVT)  → valCN (proj₁ (argVT n)) → valCN (proj₂ (argVT n)) → Set
  valVT take = _*take_
  valVT read = _*read_
  
  valAdj : (n : nameAdj) → valCN (argAdj n) → Set
  valAdj ()
  
  val<:0 : ∀{n1 n2} → {{n1 <:0 n2}} → valCN n1 ⟦<:⟧ valCN n2
  val<:0 {Human} {Human} = Idc
  val<:0 {Info} {Info} = Idc
  val<:0 {Phys} {Phys} = Idc
  val<:0 {Book} {Info} = BIc
  val<:0 {Book} {Phys} = BPc
  val<:0 {Book} {Book} = Idc
  
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
  
  _ : ⟦s s1 ⟧ ≡ ⟪ *John ⟫ *take ⟪ *War-and-Peace ⟫
  _ = refl 
  
  s2 = s-nv (np-pn John) (vp-vt read (np-pn War-and-Peace)) 
  
  _ : ⟦s s2 ⟧ ≡ ⟪ *John ⟫ *read ⟪ *War-and-Peace ⟫
  _ = refl
  
  -- John take a book
  s3 = s-nv (np-pn John) (vp-vt take (np-det a/an (cn-n Book)))
  
  _ : ⟦s s3 ⟧ ≡ Σ *Book λ b → ⟪ *John ⟫ *take ⟪ b ⟫
  _ = refl
  
  _ : ⟦s s3 ⟧ ≡ (Σ[ b ∈ *Book ] ⟪ *John ⟫ *take ⟪ b ⟫)
  _ = refl
  
  -- John read every book
  s4 = s-nv (np-pn John) (vp-vt read (np-det every (cn-n Book)))
  
  _ : ⟦s s4 ⟧ ≡ ∀ (b : *Book) →  ⟪ *John ⟫ *read ⟪ b ⟫
  _ = refl
  
  
