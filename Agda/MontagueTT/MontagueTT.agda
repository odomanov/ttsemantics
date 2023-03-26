-- Montague semantics in terms of TT.
-- Without coercion.

-- Здесь не соблюдается параллельность синтаксиса и семантики, которая есть
-- у Монтегю.  В частности, синтаксические категории понимаются не как
-- функции, а как типы, имеющие свои конструкторы.

module _ where

open import Data.Empty
open import Data.List hiding (head)
open import Data.Product
open import Data.Unit
open import Relation.Nullary renaming (no to not)
open import Relation.Binary.PropositionalEquality

-- Синтаксические категории.
-- ========================

-- Проверка согласования типов производится на уровне синтаксиса.
-- Это не обязательно должно быть так.  Например, при этой формализации исключаются
-- фразы типа "Зелёные идеи яростно спят", т.е. правильные синтаксически, но
-- неправильные семантически.

mutual

  -- CN ни от чего не зависит
  data CN : Set where
    Human Dog Unicorn : CN
    cn-ap : ∀ {cn} → AP cn → CN        -- пример: big Dog
    rcn : (cn : CN) → VP cn → CN       -- CN that VP

  -- VI зависит от CN
  data VI : CN → Set where
    runs : VI Human              -- runs применимо к Human

  data VT : CN → CN → Set where
    love : VT Human Human
    seek : VT Human Unicorn

  -- PN зависит от CN
  data PN : CN → Set where
    Alex Mary John : PN Human    -- Alex, Mary, John относятся к Human
    Polkan : PN Dog              -- Polkan относится к Dog
  
  data DET : Set where
    a/an every no the : DET

  data Adj : CN → Set where
    big : Adj Dog

  -- VP зависит от CN (к чему применима глагольная группа VP)
  data VP (cn : CN) : Set where
    vp-vi : VI cn → VP cn
    vp-vt : ∀ {cn2} → VT cn cn2 → NP cn2 → VP cn

  -- NP зависит от CN (к какому CN относится NP)
  data NP : (cn : CN) → Set where
    np-pn  : ∀ {cn} → PN cn → NP cn
    np-det : DET → (cn : CN) → NP cn
  
  data AP (cn : CN) : Set where
    ap-a  : Adj cn → AP cn
    ap-ap : Adj cn → AP cn → AP cn

  
  -- в предложении NP и VP должны зависеть от одного и того же CN
  data S : Set where
    s-nvp  : ∀ {cn} → NP cn → VP cn → S
    s-nvn  : ∀ {cn1 cn2} → NP cn1 → VT cn1 cn2 → NP cn2 → S
    s-nvn2 : ∀ {cn1 cn2} → NP cn2 → VT cn1 cn2 → NP cn1 → S   -- для пассива


-- Семантика
-- =========

-- Звёздочкой в начале обозначаем то, что относится к онтологии -- объекты,
-- функции на них и пр.

postulate
  *Human *Dog *Unicorn : Set
  *Alex *Mary *John : *Human
  *Polkan : *Dog
  _*runs  : *Human → Set
  _*love_ : *Human → *Human → Set
  _*seek_ : *Human → *Unicorn → Set
  *big    : *Dog → Set 

-- тип A с выделенным элементом  -- нужен для определения 'the'
record Pointed (A : Set) : Set where
  field
    theₚ : A
open Pointed    


-- Определяем функции интерпретации для всех синтаксических категорий.

mutual

  ⟦cn_⟧ : CN → Set                        -- CN ≠ e → t !  CN это тип.
  ⟦cn Human ⟧ = *Human
  ⟦cn Dog ⟧ = *Dog
  ⟦cn Unicorn ⟧ = *Unicorn
  ⟦cn cn-ap (ap-a big) ⟧ = Σ *Dog *big
  ⟦cn cn-ap {cn} ap ⟧ = Σ ⟦cn cn ⟧ ⟦ap ap ⟧   
  ⟦cn rcn cn vp ⟧ = Σ ⟦cn cn ⟧ ⟦vp vp ⟧
  
  ⟦pn_⟧ : {cn : CN} → PN cn → ⟦cn cn ⟧
  ⟦pn Alex ⟧   = *Alex
  ⟦pn Mary ⟧   = *Mary
  ⟦pn John ⟧   = *John
  ⟦pn Polkan ⟧ = *Polkan

  ⟦np_⟧ : {cn : CN} → NP cn → (⟦cn cn ⟧ → Set) → Set   -- NP = (e → t) → t     
  ⟦np np-pn pn ⟧ ⟦vp⟧ = ⟦vp⟧ ⟦pn pn ⟧
  ⟦np np-det d cn ⟧ ⟦vp⟧ = ⟦det d ⟧ cn ⟦vp⟧
  
  ⟦vi_⟧ : {cn : CN} → VI cn → ⟦cn cn ⟧ → Set           -- VI = e → t
  ⟦vi runs ⟧ = _*runs
  
  ⟦vt_⟧ : ∀ {cn cn1} → VT cn cn1 → ⟦cn cn ⟧ → ⟦cn cn1 ⟧ → Set    -- VT = e → e → t
  ⟦vt love ⟧ = _*love_
  ⟦vt seek ⟧ = _*seek_

  ⟦vp_⟧ : {cn : CN} → VP cn → ⟦cn cn ⟧ → Set             -- VP = e → t
  ⟦vp vp-vi runs ⟧ = _*runs
  ⟦vp vp-vt vt np ⟧ x = ⟦np np ⟧ λ y → ⟦vt vt ⟧ x y              -- λx.(NP (λy.(VT x y)))

  ⟦det_⟧ : DET → (cn : CN)→ (⟦cn cn ⟧ → Set) → Set       -- DET = (e → t) → ((e → t) → t) 
  ⟦det a/an ⟧  cn ⟦vp⟧ = Σ ⟦cn cn ⟧ ⟦vp⟧ 
  ⟦det every ⟧ cn ⟦vp⟧ = (x : ⟦cn cn ⟧) → ⟦vp⟧ x
  ⟦det no ⟧    cn ⟦vp⟧ = (x : ⟦cn cn ⟧) → ¬ ⟦vp⟧ x 
  ⟦det the ⟧   cn ⟦vp⟧ = Σ[ Aₚ ∈ Pointed ⟦cn cn ⟧ ] ⟦vp⟧ (theₚ Aₚ)
  
  {-# TERMINATING #-}
  ⟦ap_⟧ : {cn : CN} → AP cn → (⟦cn cn ⟧ → Set)           -- AP = (e → t) 
  ⟦ap ap-a big ⟧ = *big
  ⟦ap_⟧ {cn} (ap-ap adj ap) x = Σ[ y ∈ Σ ⟦cn cn ⟧ ⟦ap ap-a adj ⟧ ] ⟦ap ap ⟧ (proj₁ y)

  -- Возможны множественные интерпретации.
  ⟦s_⟧ : S → List Set
  ⟦s s-nvp np vp ⟧ = ⟦np np ⟧ ⟦vp vp ⟧ ∷ []
  ⟦s s-nvn np1 vt np2 ⟧ = ⟦np np1 ⟧ (λ x → (⟦np np2 ⟧ λ y → ⟦vt vt ⟧ x y)) -- = ⟦np np1 ⟧ ⟦vp vp-vt vt np2 ⟧
                        ∷ ⟦np np2 ⟧ (λ x → (⟦np np1 ⟧ λ y → ⟦vt vt ⟧ y x))
                        ∷ []
  ⟦s s-nvn2 np1 vt np2 ⟧ = ⟦np np1 ⟧ (λ x → (⟦np np2 ⟧ λ y → ⟦vt vt ⟧ y x))
                         ∷ ⟦np np2 ⟧ (λ x → (⟦np np1 ⟧ λ y → ⟦vt vt ⟧ x y))
                         ∷ []

-- проверим равенство
_ : ∀ {cn1 cn2}{np1 : NP cn1}{np2 : NP cn2}{vt : VT cn1 cn2}
    → ⟦np np1 ⟧ (λ x → (⟦np np2 ⟧ λ y → ⟦vt vt ⟧ x y)) ≡ ⟦np np1 ⟧ ⟦vp vp-vt vt np2 ⟧
_ = refl



-- Примеры
-- -------

s1 = s-nvp (np-pn Mary) (vp-vi runs)

_ : ⟦s s1 ⟧ ≡ *Mary *runs ∷ [] 
_ = refl



-- s3 = s-nvp (np-pn Polkan) (vp-vi runs)     -- это не работает! нужна коэрсия


-- a human runs
s4 = s-nvp (np-det a/an Human) (vp-vi runs)

_ : ⟦s s4 ⟧ ≡ Σ *Human _*runs ∷ []
_ = refl


-- every human runs
s5 = s-nvp (np-det every Human) (vp-vi runs)

_ : ⟦s s5 ⟧ ≡ ((x : *Human) → x *runs) ∷ []
_ = refl



-- the human runs
s6 = s-nvp (np-det the Human) (vp-vi runs)

_ : ⟦s s6 ⟧ ≡ (Σ[ Aₚ ∈ Pointed *Human ] (theₚ Aₚ) *runs) ∷ []
_ = refl


-- вспомогательные функции
inhabited : ∀ {a} {A : Set a} → List A → Set
inhabited [] = ⊥
inhabited _  = ⊤

head : ∀ {a}{A : Set a} → (l : List A) → {_ : inhabited l} → A
head (x ∷ _) = x   


_ : head ⟦s s6 ⟧
_ = Hₚ , *Mary-runs
  where
  Hₚ : Pointed *Human 
  Hₚ = record { theₚ = *Mary }

  postulate *Mary-runs : *Mary *runs



-- Прилагательные / свойства

big-dog : ⟦cn cn-ap (ap-a big) ⟧ 
big-dog = *Polkan , *polkan-is-big 
  where postulate *polkan-is-big : *big *Polkan



-- Относительные конструкции (CN that VP и пр.)

human-that-runs : CN
human-that-runs = rcn Human (vp-vi runs)

_ : ⟦cn human-that-runs ⟧
_ = *Mary , *Mary-runs
  where postulate *Mary-runs : *Mary *runs 


a-human-that-runs : NP _ 
a-human-that-runs = np-det a/an human-that-runs


--s9 = s-nvp a-human-that-runs (vp-vi runs)   -- не работает!  нужна коэрсия



-- Mary loves Alex

s11 = s-nvp (np-pn Mary) (vp-vt love (np-pn Alex))

_ : ⟦s s11 ⟧ ≡ *Mary *love *Alex ∷ []          
_ = refl


-- Mary loves a human

s12 = s-nvp (np-pn Mary) (vp-vt love (np-det a/an Human))

_ : ⟦s s12 ⟧ ≡ (Σ[ x ∈ *Human ] *Mary *love x) ∷ []
_ = refl


-- Every human loves a human (possibly different)   -- ср. s17

s13 = s-nvp (np-det every Human) (vp-vt love (np-det a/an Human))

_ : ⟦s s13 ⟧ ≡ (∀ (x : *Human) → Σ[ y ∈ *Human ] (x *love y)) ∷ []
_ = refl



-- Двусмысленное предложение:
-- Every human loves a human

s17 = s-nvn (np-det every Human) love (np-det a/an Human)

_ : ⟦s s17 ⟧ ≡ (∀ (x : *Human) → Σ[ y ∈ *Human ] (x *love y))  -- x love different humans
             ∷ (Σ[ y ∈ *Human ] (∀ (x : *Human) → x *love y))  -- x love the same human
             ∷ []
_ = refl

-- то же в пассиве
-- Every human is loved by a human
s18 = s-nvn2 (np-det every Human) love (np-det a/an Human)

_ : ⟦s s18 ⟧ ≡ ((x : *Human) → Σ[ y ∈ *Human ] y *love x)
             ∷ (Σ[ y ∈ *Human ] ∀ (x : *Human) → y *love x)
             ∷ []
_ = refl


-- То же, но с одним квантором.
-- John seeks a unicorn.
s18a = s-nvn (np-pn John) seek (np-det a/an Unicorn)

_ : ⟦s s18a ⟧ ≡ (Σ[ x ∈ *Unicorn ] *John *seek x)   -- у нас интерпретации совпадают; Монтегю для описания
              ∷ (Σ[ x ∈ *Unicorn ] *John *seek x)   -- различий использует интенсиональную логику.
              ∷ []
_ = refl

-- A unicorn is sought by John.
s18b = s-nvn2 (np-det a/an Unicorn) seek (np-pn John)

_ : ⟦s s18b ⟧ ≡ (Σ[ x ∈ *Unicorn ] *John *seek x)
              ∷ (Σ[ x ∈ *Unicorn ] *John *seek x)
              ∷ []
_ = refl



-- НО!
-- Два смысла предложения могут и совпадать:

s19 = s-nvn (np-pn Mary) love (np-pn Alex)

_ : ⟦s s19 ⟧ ≡ (*Mary *love *Alex)
             ∷ (*Mary *love *Alex)
             ∷ []
_ = refl            


-- то же в пассиве
s20 = s-nvn2 (np-pn Mary) love (np-pn Alex)

_ : ⟦s s20 ⟧ ≡ (*Alex *love *Mary)
             ∷ (*Alex *love *Mary)
             ∷ []
_ = refl            

