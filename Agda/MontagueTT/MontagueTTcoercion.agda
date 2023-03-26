-- Montague semantics in terms of TT.
-- With coercion.

open import Data.Product
open import Function
open import Relation.Nullary renaming (no to not)
open import Relation.Binary.PropositionalEquality
open import Coercion renaming (_<:_ to _⟦<:⟧_)

module _ where

-- Синтаксические категории.
-- ========================

mutual

  data CN : Set where
    Human Dog Animate Object : CN
    cn-ap : ∀ {cn} → AP cn → (cn1 : CN) → {{coe : cn1 <: cn}} → CN
    rcn   : (cn : CN) {cn1 : CN} → {{coe : cn <: cn1}} → VP cn1 → CN    -- CN that VP
    
  data _<:_ : CN → CN → Set where
    instance cha  : Human <: Animate
    instance cda  : Dog <: Animate
    instance cao  : Animate <: Object
    instance cho  : Human <: Object
    instance cdo  : Dog <: Object
    instance ccc  : ∀ {cn} → cn <: cn
    instance crcn : ∀ {cn cn1 coe vp} → rcn cn {cn1} {{coe}} vp <: cn
    c∘   : ∀ {cn cn1 cn2} → cn <: cn1 → cn1 <: cn2 → cn <: cn2

  data VI : CN → Set where
    runs : VI Animate

  -- порядок аргументов в VT прямой!  VT A B => A → B → Set
  data VT : CN → CN → Set where
    love : VT Animate Object
    
  data PN : CN → Set where
    Alex Mary : PN Human
    Polkan    : PN Dog
  
  data DET : Set where
    a/an every no the : DET

  data Adj : CN → Set where
    big small : Adj Object
    
  -- порядок аргументов в VT прямой!
  data VP (cn : CN) : Set where
    vp-vi : VI cn → VP cn
    vp-vt : ∀ {cn1 cn2} → VT cn cn1 → {{coe : cn2 <: cn1}} → NP cn2 → VP cn
  
  data NP : (cn : CN) → Set where
    np-pn  : ∀ {cn} → PN cn → NP cn
    np-det : DET → (cn : CN) → NP cn
  
  data AP (cn : CN) : Set where
    ap-a : Adj cn → AP cn
    
  data S : Set where
    s-nv  : ∀ {cn} → NP cn → ∀ {cn1} → {{coe : cn <: cn1}} → VP cn1 → S

instance
  crcn-ha : ∀ {cn1 coe vp} → rcn Human {cn1} {{coe}} vp <: Animate
  crcn-ha = c∘ crcn cha

  crcn-ao : ∀ {cn1 coe vp} → rcn Human {cn1} {{coe}} vp <: Object
  crcn-ao = c∘ (crcn-ha) cao

-- Семантика
-- =========

postulate
  *Human *Dog *Animate *Object : Set
  *Alex *Mary : *Human
  *Polkan     : *Dog
  _*runs      : *Animate → Set
  _*love_     : *Animate → *Object → Set
  *big        : *Object → Set
  *small      : *Object → Set 

postulate
  fDA : *Dog → *Animate
  fHA : *Human → *Animate
  fAO : *Animate → *Object
  
instance
  Ac : ∀ {ℓ} {A : Set ℓ} → A ⟦<:⟧ A
  Ac = identityCoercion
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
  
-- тип A с выделенным элементом  -- нужен для определения 'the'
record Pointed (A : Set) : Set where
  field
    theₚ : A
open Pointed    

mutual

  ⟦cn_⟧ : CN → Set                        -- CN ≠ e → t !  CN это тип.
  ⟦cn Human ⟧ = *Human
  ⟦cn Dog ⟧ = *Dog
  ⟦cn Animate ⟧ = *Animate
  ⟦cn Object ⟧ = *Object
  ⟦cn cn-ap ap cn {{coe}} ⟧ = ⟪Σ⟫ ⟦cn cn ⟧ ⟦ap ap ⟧ {{⟦coe coe ⟧}}  
  ⟦cn rcn cn {{coe = coe}} vp ⟧ = ⟪Σ⟫ ⟦cn cn ⟧ ⟦vp vp ⟧ {{⟦coe coe ⟧}} 

  ⟦coe_⟧ : {cn cn1 : CN} → (cn <: cn1) → (⟦cn cn ⟧ ⟦<:⟧ ⟦cn cn1 ⟧)
  ⟦coe cha ⟧ = HAc
  ⟦coe cda ⟧ = DAc
  ⟦coe cao ⟧ = AOc
  ⟦coe cho ⟧ = HOc    
  ⟦coe cdo ⟧ = DOc
  ⟦coe ccc ⟧ = Ac
  ⟦coe crcn ⟧ = refinementCoercion 
  ⟦coe c∘ c12 c23 ⟧ = ⟦coe c23 ⟧ ⟪∘⟫ ⟦coe c12 ⟧  

  ⟦pn_⟧ : {cn : CN} → PN cn → ⟦cn cn ⟧
  ⟦pn Alex ⟧   = *Alex 
  ⟦pn Mary ⟧   = *Mary 
  ⟦pn Polkan ⟧ = *Polkan 
  
  ⟦np_⟧ : {cn cn1 : CN} → NP cn →
        {{cc : ⟦cn cn ⟧ ⟦<:⟧ ⟦cn cn1 ⟧}} → (⟦cn cn1 ⟧ → Set) → Set  -- NP = (e → t) → t
  ⟦np np-pn pn ⟧    ⟦vp⟧ = ⟦vp⟧ ⟪ ⟦pn pn ⟧ ⟫
  ⟦np np-det d cn ⟧ ⟦vp⟧ = ⟦det d ⟧ cn ⟦vp⟧
  
  ⟦vi_⟧ : {cn : CN} → VI cn → ⟦cn cn ⟧ → Set           -- VI = e → t
  ⟦vi runs ⟧ = _*runs

  ⟦vt_⟧ : ∀ {cn cn1} → VT cn cn1 → ⟦cn cn ⟧ → ⟦cn cn1 ⟧ → Set     -- VT = e → e → t
  ⟦vt love ⟧ = _*love_

  {-# TERMINATING #-}
  ⟦vp_⟧ : {cn0 cn01 : CN} → VP cn0 → {{cc : ⟦cn cn01 ⟧ ⟦<:⟧ ⟦cn cn0 ⟧}}
        → ⟦cn cn01 ⟧ → Set   -- VP = e → t
  -- ⟦vp copula ⟧ = {!!}
  ⟦vp vp-vi vi ⟧ x = ⟦vi vi ⟧ ⟪ x ⟫
  ⟦vp vp-vt vt {{coe}} np ⟧ x =
    ⟦np np ⟧ λ y → ⟦vt vt ⟧ ⟪ x ⟫ (⟪ y ⟫ {{⟦coe coe ⟧}})   -- λx.(NP (λy.(VT y x)))


  -- DET = (e → t) → ((e → t) → t) 
  ⟦det_⟧ : DET → (cn : CN) → {cn1 : CN} → {{_ : ⟦cn cn ⟧ ⟦<:⟧ ⟦cn cn1 ⟧}}
         → (⟦cn cn1 ⟧ → Set) → Set 
  ⟦det a/an ⟧  cn ⟦vp⟧ = Σ ⟦cn cn ⟧ ⟪→ ⟦vp⟧ ⟫ 
  ⟦det every ⟧ cn ⟦vp⟧ = (x : ⟦cn cn ⟧) → ⟦vp⟧ ⟪ x ⟫
  ⟦det no ⟧    cn ⟦vp⟧ = (x : ⟦cn cn ⟧) → ¬ ⟦vp⟧ ⟪ x ⟫ 
  ⟦det the ⟧   cn ⟦vp⟧ = Σ[ Aₚ ∈ Pointed ⟦cn cn ⟧ ] ⟦vp⟧ ⟪ theₚ Aₚ ⟫
  
  ⟦ap_⟧ : {cn : CN} → AP cn → (⟦cn cn ⟧ → Set)        -- AP = (e → t) 
  ⟦ap ap-a big ⟧ = *big
  ⟦ap ap-a small ⟧ = *small
  
  ⟦s_⟧ : S → Set
  ⟦s s-nv np {{coe = coe}} vp ⟧ = ⟦np np ⟧ (⟪→ ⟦vp vp ⟧ ⟫ {{⟦coe coe ⟧}})



s1 = s-nv (np-pn Mary) (vp-vi runs)

_ : ⟦s s1 ⟧ ≡  ⟪ *Mary ⟫ *runs
_ = refl



s3 = s-nv (np-pn Polkan) (vp-vi runs)     -- coercion works


-- a human runs
s4 = s-nv (np-det a/an Human) (vp-vi runs)

_ : ⟦s s4 ⟧ ≡ ⟪Σ⟫ *Human _*runs 
_ = refl


-- every human runs
s5 = s-nv (np-det every Human) (vp-vi runs)

_ : ⟦s s5 ⟧ ≡ ((x : *Human) → ⟪ x ⟫ *runs)
_ = refl



-- the human runs
s6 = s-nv (np-det the Human) (vp-vi runs)

_ : ⟦s s6 ⟧
_ = Hₚ , *Mary-runs
  where
  Hₚ : Pointed *Human 
  Hₚ = record { theₚ = *Mary }

  postulate *Mary-runs : ⟪ *Mary ⟫ *runs



-- Прилагательные / свойства

postulate
  *polkan-is-big : *big ⟪ *Polkan ⟫

big-dog : ⟦cn cn-ap (ap-a big) Dog ⟧ 
big-dog = *Polkan , *polkan-is-big 


-- Относительные конструкции (CN that VP и пр.)

human-that-runs : CN
human-that-runs = rcn Human (vp-vi runs)

_ : ⟦cn human-that-runs ⟧
_ = *Mary , *Mary-runs
  where postulate *Mary-runs : ⟪ *Mary ⟫ *runs 


a-human-that-runs : NP _ 
a-human-that-runs = np-det a/an human-that-runs

-- a human that runs runs
s9 = s-nv a-human-that-runs (vp-vi runs)   -- coercion in action 



-- Mary loves Alex

loves-Alex : VP _
loves-Alex = vp-vt love (np-pn Alex)

s11 = s-nv (np-pn Mary) loves-Alex

_ : ⟦s s11 ⟧ ≡ ⟪ *Mary ⟫ *love ⟪ *Alex ⟫
_ = refl


-- Mary loves Polkan

s12 = s-nv (np-pn Mary) (vp-vt love (np-pn Polkan))

_ : ⟦s s12 ⟧ ≡ ⟪ *Mary ⟫ *love ⟪ *Polkan ⟫
_ = refl


-- Mary loves a human that runs

s13 = s-nv (np-pn Mary) (vp-vt love a-human-that-runs)

_ : ⟦s s13 ⟧ ≡ (Σ[ p ∈ Σ[ h ∈ *Human ] ⟪ h ⟫ *runs ] ⟪ *Mary ⟫ *love ⟪ proj₁ p ⟫)
_ = refl

