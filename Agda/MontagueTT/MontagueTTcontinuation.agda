{-# OPTIONS --cumulativity #-}
-- Montague semantics in terms of TT (без прилагательных и относительных конструкций).
-- Without coercion, with continuations.

-- Здесь не соблюдается параллельность синтаксиса и семантики, которая есть
-- у Монтегю.  В частности, синтаксические категории понимаются не как
-- функции, а как типы, имеющие свои конструкторы.

module _ where

open import Data.Empty
open import Data.Fin using (#_)
open import Data.List hiding (head)
open import Data.Product
open import Data.Unit
open import Function
open import Relation.Nullary renaming (no to not)
open import Relation.Binary.PropositionalEquality
open import Level 
1ℓ = suc 0ℓ
2ℓ = suc 1ℓ

-- Continuation monad

open import Category.Monad
open import Category.Monad.Indexed
open import Category.Monad.Continuation

Cont : ∀{a b}(R : Set a) → Set (a ⊔ b) → Set (a ⊔ b)
Cont R = DCont id R R  

MonadICont : ∀{a}{b}(R : Set a) → RawIMonad (DCont {f = a ⊔ b} id)  
MonadICont R = DContIMonad id 

-- проверим монадные законы
module Laws {a} {b} {R : Set a} where

  open RawIMonad (MonadICont {a} {b} R)
  
  unitl : ∀{A B : Set b}{x : A}{f : A → Cont {a} {b} R B}
    → (return x >>= f) ≡ f x
  unitl = refl

  unitr : ∀{A R}{ma : Cont R A}
    → (ma >>= return) ≡ ma
  unitr = refl

  assoc : ∀{A B C : Set b} 
    → {ma : Cont {a} {b} R A} {f : A → Cont {a} {b} R B} {g : B → Cont {a} {b} R C}  
    → ((ma >>= f) >>= g) ≡ (ma >>= (λ a → f a >>= g))
  assoc = refl

  assoc' : ∀{A B C D : Set b} 
    → {f : A → Cont {a} {b} R B} {g : B → Cont {a} {b} R C} {h : C → Cont {a} {b} R D}  
    → ((f >=> g) >=> h) ≡ (f >=> (g >=> h))
  assoc' = refl

  
open RawIMonad (MonadICont Set) 


-- The structure to hold names
-- ===========================

record LexStructure : Set₁ where
  field
    nameCN namePN nameVA nameVI nameVT nameAdj : Set  -- names for syntactic categories
    argPN  : namePN  → nameCN                  -- argument types etc.
    argVI  : nameVI  → nameCN
    argVA  : nameVA  → nameCN                  -- attitude verbs
    argVT  : nameVT  → nameCN × nameCN
    argAdj : nameAdj → nameCN


-- Синтаксические категории.
-- ========================

-- Проверка согласования типов производится на уровне синтаксиса.
-- Это не обязательно должно быть так.  Например, при этой формализации исключаются
-- фразы типа "Зелёные идеи яростно спят", т.е. правильные синтаксически, но
-- неправильные семантически.

module Syntax (nam : LexStructure) where

  open LexStructure nam 
  
  mutual
  
    -- CN ни от чего не зависит
    data CN : Set where
      cn-n : nameCN → CN
      -- cn-ap : ∀ {cn} → AP cn → CN        -- пример: black Dog
      -- rcn : (cn : CN) → VP cn → CN       -- CN that VP
  
    -- -- VI зависит от CN
    data VI : CN → Set where
      vi-n : (n : nameVI) → VI $ cn-n $ argVI n

    -- attitude verbs -- a la 'believe'
    data VA : CN → Set where
      va-n : (n : nameVA) → VA $ cn-n $ argVA n 
  
    data VT : CN → CN → Set where
      vt-n : (n : nameVT) → VT (cn-n (proj₁ (argVT n))) (cn-n (proj₂ (argVT n))) 
  
    -- PN зависит от CN
    data PN : CN → Set where
      pn-n : (n : namePN) → PN $ cn-n $ argPN n
    
    -- data Adj : CN → Set where
    --   black : Adj Dog
  
    data DET : Set where
      a/an every no the : DET
  
    -- VP зависит от CN (к чему применима глагольная группа VP)
    data VP : (cn : CN) → Set where
      vp-vi : ∀{cn} → VI cn → VP cn 
      vp-vt : ∀{cn1 cn2} → VT cn1 cn2 → NP cn2 → VP cn1
  
    -- NP зависит от CN (к какому CN относится NP)
    data NP : (cn : CN) → Set where
      np-pn  : (n : namePN) → NP $ cn-n $ argPN n
      np-det : DET → (cn : CN) → NP cn
    
    -- data AP : (cn : CN) → Set where
    --   ap-a  : (n : nameAdj) → AP $ cn-n $ argAdj n
    --   -- ap-ap : Adj cn → AP cn → AP cn
  
    
    -- в предложении NP и VP должны зависеть от одного и того же CN
    data S : Set where
      s-nvp  : ∀ {cn} → NP cn → VP cn → S
      s-vt   : ∀ {cn1 cn2} → NP cn1 → VT cn1 cn2 → NP cn2 → S
      s-vtp  : ∀ {cn1 cn2} → NP cn2 → VT cn1 cn2 → NP cn1 → S   -- для пассива
      s-va   : ∀ {cn1} → NP cn1 → VA cn1 → S → S


-- Семантика
-- =========

record Model (nam : LexStructure) : Setω where
  open LexStructure nam 
  field
    valCN  : nameCN → Set
    valPN  : (n : namePN)  → valCN (argPN n) 
    valVI  : (n : nameVI)  → valCN (argVI n) → Set
    valVA  : (n : nameVA)  → (h : valCN (argVA n))
                           → ∀{a}(A : Set a)(P : A → Set) → Set a 
    valVT  : (n : nameVT)  → valCN (proj₁ (argVT n))
                           → valCN (proj₂ (argVT n)) → Set
    valAdj : (n : nameAdj) → valCN (argAdj n) → Set


module Semantics (nam : LexStructure) (m : Model nam) where

  open LexStructure nam 
  open Syntax nam 
  open Model m 

  -- тип A с выделенным элементом  -- нужен для определения 'the'
  record Pointed (A : Set) : Set where
    field
      theₚ : A
  open Pointed public
  
  
  -- Определяем функции интерпретации для всех синтаксических категорий.
  
  mutual
  
    ⟦cn_⟧ : CN → Set                        -- CN ≠ e → t !  CN это тип.
    ⟦cn cn-n n ⟧ = valCN n
    -- ⟦cn cn-ap (ap-a n) ⟧ = Σ ⟦cn cn-n (argAdj n) ⟧ ⟦ap ap-a n ⟧
    -- -- ⟦cn cn-ap {cn} ap ⟧ = Σ ⟦cn cn ⟧ ⟦ap ap ⟧   
    -- ⟦cn rcn cn vp ⟧ = Σ ⟦cn cn ⟧ ⟦vp vp ⟧
    
    ⟦pn_⟧ : {cn : CN} → PN cn → ⟦cn cn ⟧
    ⟦pn pn-n n ⟧   = valPN n
  
    -- NP = (e → t) → t     
    ⟦np_⟧ : {cn : CN} → NP cn → Cont Set ⟦cn cn ⟧
    ⟦np np-pn pn ⟧ = return ⟦pn pn-n pn ⟧
    ⟦np np-det d cn ⟧ = ⟦det d ⟧ cn    
    
    _⟦va_⟧ : ∀{cn1} → ⟦cn cn1 ⟧ → VA cn1 → (A : Set) → Cont Set A
    (h ⟦va (va-n n) ⟧) A = λ k → valVA n h A λ x → k x 
    
    -- VI = e → t
    ⟦vi_⟧ : {cn : CN} → VI cn → ⟦cn cn ⟧ → Cont Set Set
    ⟦vi vi-n n ⟧ x = return $ valVI n x

    -- VT = e → e → t
    ⟦vt_⟧ : ∀ {cn cn1} → VT cn cn1 → ⟦cn cn ⟧ → ⟦cn cn1 ⟧ → Cont Set Set
    ⟦vt vt-n n ⟧ x y = return $ valVT n x y
  
    -- VP = e → t
    ⟦vp_⟧ : {cn : CN} → VP cn → ⟦cn cn ⟧ → Cont Set Set
    ⟦vp vp-vi (vi-n v) ⟧ x = return $ valVI v x
    ⟦vp vp-vt vt np ⟧ x = do y ← ⟦np np ⟧
                             ⟦vt vt ⟧ x y

    -- DET = (e → t) → ((e → t) → t) 
    ⟦det_⟧ : DET → (cn : CN)→ Cont Set ⟦cn cn ⟧
    ⟦det a/an ⟧  cn = λ k → Σ[ x ∈ ⟦cn cn ⟧ ] k x 
    ⟦det every ⟧ cn = λ k → ∀(x : ⟦cn cn ⟧) → k x
    ⟦det no ⟧    cn = λ k → ∀(x : ⟦cn cn ⟧) → ¬ k x 
    ⟦det the ⟧   cn = λ k → Σ[ Aₚ ∈ Pointed ⟦cn cn ⟧ ] k (theₚ Aₚ)
    
    -- {-# TERMINATING #-}
    -- ⟦ap_⟧ : {cn : CN} → AP cn → (⟦cn cn ⟧ → Set)           -- AP = (e → t) 
    -- ⟦ap ap-a n ⟧ = valAdj n
    -- -- ⟦ap_⟧ {cn} (ap-ap adj ap) x = Σ[ y ∈ Σ ⟦cn cn ⟧ ⟦ap ap-a adj ⟧ ] ⟦ap ap ⟧ (proj₁ y)
  
    -- Возможны множественные интерпретации.
    ⟦s_⟧ : S → List (Cont Set Set)
    ⟦s s-nvp np vp ⟧ = (do x ← ⟦np np ⟧
                           ⟦vp vp ⟧ x) ∷ []
    ⟦s s-vt np1 vt np2 ⟧ = (do x ← ⟦np np1 ⟧
                               y ← ⟦np np2 ⟧
                               ⟦vt vt ⟧ x y   )
                         ∷ (do y ← ⟦np np2 ⟧
                               x ← ⟦np np1 ⟧
                               ⟦vt vt ⟧ x y   ) ∷ []
    ⟦s s-vtp np1 vt np2 ⟧ = (do x ← ⟦np np1 ⟧                       -- passive
                                y ← ⟦np np2 ⟧
                                ⟦vt vt ⟧ y x   )
                          ∷ (do y ← ⟦np np2 ⟧
                                x ← ⟦np np1 ⟧
                                ⟦vt vt ⟧ y x   ) ∷ []
    ⟦s s-va np1 va (s-nvp {cn2} np2 vp2) ⟧ =
          (do x ← ⟦np np2 ⟧
              y ← ⟦np np1 ⟧
              (y ⟦va va ⟧) ⟦cn cn2 ⟧
              ⟦vp vp2 ⟧ x
      ) ∷ (do y ← ⟦np np1 ⟧
              x ← (y ⟦va va ⟧) ⟦cn cn2 ⟧
              ⟦vp vp2 ⟧ x
      ) ∷ []
    ⟦s s-va np1 va (s-vt np2 vt np3) ⟧ = []           -- TODO
    -- ⟦s s-va np1 va (s-vt {cn2} {cn3} np2 vt np3) ⟧ =
    --     (do x ← ⟦np np2 ⟧
    --         y ← ⟦np np1 ⟧
    --         (y ⟦va va ⟧) ⟦cn cn3 ⟧
    --         ⟦vp (vp-vt vt np3) ⟧ x)
    --   ∷ (do y ← ⟦np np1 ⟧
    --         x ← (y ⟦va va ⟧) ⟦cn cn2 ⟧
    --         ⟦vp (vp-vt vt np3) ⟧ x   ) ∷ []
    ⟦s s-va np1 va (s-vtp vt np2 np3) ⟧ = []                       -- TODO
    ⟦s s-va np1 va (s-va np2 va2 s2) ⟧ = []                        -- TODO
  

-- Примеры
-- -------

-- Name structure

data nameCN  : Set where Human Dog Unicorn : nameCN
data namePN  : Set where Alex Mary John Polkan Ralph : namePN
data nameVI  : Set where run exists is-spy : nameVI
data nameVA  : Set where
  believe : nameVA
  seek : nameVA
data nameVT  : Set where love : nameVT
data nameAdj : Set where black : nameAdj

argPN : namePN → nameCN
argPN Alex = Human
argPN Mary = Human
argPN John = Human
argPN Ralph = Human
argPN Polkan = Dog

argVI : nameVI → nameCN
argVI run = Human
argVI is-spy = Human
argVI exists = Unicorn

argVA : nameVA → nameCN 
argVA believe = Human 
argVA seek = Human 

argVT : nameVT → nameCN × nameCN
argVT love = Human , Human

argAdj : nameAdj → nameCN
argAdj black   = Dog
  
-- Звёздочкой в начале обозначаем то, что относится к онтологии -- объекты,
-- функции на них и пр.

postulate
  *Human *Dog *Unicorn : Set
  *Alex *Mary *John *Ralph : *Human
  *Polkan  : *Dog
  _*run    : *Human → Set
  _*is-spy : *Human → Set
  _*exists : *Unicorn → Set
  _*love_  : *Human → *Human → Set
  *black   : *Dog → Set

L : LexStructure
L = record
      { nameCN = nameCN
      ; namePN = namePN
      ; nameVI = nameVI
      ; nameVA = nameVA
      ; nameVT = nameVT
      ; nameAdj = nameAdj
      ; argPN = argPN
      ; argVI = argVI
      ; argVA = argVA
      ; argVT = argVT
      ; argAdj = argAdj
      }

open Syntax L

valCN : nameCN → Set
valCN Human = *Human
valCN Dog = *Dog
valCN Unicorn = *Unicorn

valPN : (n : namePN) → valCN (argPN n) 
valPN Alex = *Alex
valPN Mary = *Mary
valPN John = *John
valPN Ralph = *Ralph
valPN Polkan = *Polkan

valVI : (n : nameVI) → valCN (argVI n) → Set
valVI run = _*run
valVI is-spy = _*is-spy
valVI exists = _*exists

--  seeks 
record seekR {H : Set}(h : H){a}(A : Set a)(P : A → Set) : Set a where
  field
    s1 : A
    s2 : P s1     

infix 2 seekR
syntax seekR h A (λ x → P) = h seek[ x ∈ A ] P

record believeR {H : Set}(h : H){a}(A : Set a)(P : A → Set) : Set a where
  field
    s1 : A
    s2 : P s1     

infix 2 believeR
syntax believeR h A (λ x → P) = h believe[ x ∈ A ] P
  
valVA : (n : nameVA) → (h : valCN (argVA n)) → ∀{a}(A : Set a)(P : A → Set) → Set a  
valVA believe = believeR 
valVA seek = seekR

valVT : (n : nameVT) → valCN (proj₁ (argVT n)) → valCN (proj₂ (argVT n)) → Set
valVT love = _*love_

valAdj : (n : nameAdj) → valCN (argAdj n) → Set
valAdj black = *black

M : Model L
M = record { valCN = valCN
           ; valPN = valPN
           ; valVI = valVI
           ; valVA = valVA
           ; valVT = valVT
           ; valAdj = valAdj }

open Semantics L M

-- вспомогательные функции
inhabited : ∀ {a} {A : Set a} → List A → Set
inhabited [] = ⊥
inhabited _  = ⊤

head : ∀ {a}{A : Set a} → (l : List A) → {_ : inhabited l} → A
head (x ∷ _) = x   


s1 = s-nvp (np-pn Mary) (vp-vi (vi-n run))

_ : head ⟦s s1 ⟧ id ≡ (*Mary *run)
_ = refl


-- -- s3 = s-nvp (np-pn Polkan) (vp-vi runs)     -- это не работает! нужна коэрсия


-- a human runs
s4 = s-nvp (np-det a/an (cn-n Human)) (vp-vi (vi-n run))

_ : head ⟦s s4 ⟧ id ≡ Σ *Human _*run
_ = refl


-- every human runs
s5 = s-nvp (np-det every (cn-n Human)) (vp-vi (vi-n run))

_ : head ⟦s s5 ⟧ id ≡ (∀(x : *Human) → x *run)
_ = refl



-- the human runs
s6 = s-nvp (np-det the (cn-n Human)) (vp-vi (vi-n run))

_ : head ⟦s s6 ⟧ id ≡ (Σ[ Aₚ ∈ Pointed *Human ] (theₚ Aₚ) *run) 
_ = refl

_ : head ⟦s s6 ⟧ id
_ = Hₚ , *Mary-runs
  where
  Hₚ : Pointed *Human 
  Hₚ = record { theₚ = *Mary }

  postulate *Mary-runs : *Mary *run



-- -- Прилагательные / свойства

-- black-dog : ⟦cn cn-ap (ap-a black) ⟧ 
-- black-dog = *Polkan , *polkan-is-black 
--   where postulate *polkan-is-black : *black *Polkan



-- -- Относительные конструкции (CN that VP и пр.)

-- human-that-runs : CN
-- human-that-runs = rcn (cn-n Human) (vp-vi run)

-- _ : ⟦cn human-that-runs ⟧
-- _ = *Mary , *Mary-runs
--   where postulate *Mary-runs : *Mary *run 


-- a-human-that-runs : NP _ 
-- a-human-that-runs = np-det a/an human-that-runs


-- --s9 = s-nvp a-human-that-runs (vp-vi runs)   -- не работает!  нужна коэрсия



-- Mary loves Alex
-- Оба смысла совпадают

s11 = s-vt (np-pn Mary) (vt-n love) (np-pn Alex)

_ : ⟦s s11 ⟧ ≡ return (*Mary *love *Alex) ∷ return (*Mary *love *Alex) ∷ []           
_ = refl


-- Mary loves a human
-- Оба смысла совпадают

s12 = s-vt (np-pn Mary) (vt-n love) (np-det a/an (cn-n Human))

_ : (lookup ⟦s s12 ⟧ (# 0)) id ≡ (Σ[ x ∈ *Human ] *Mary *love x)  
_ = refl

_ : (lookup ⟦s s12 ⟧ (# 1)) id ≡ (Σ[ x ∈ *Human ] *Mary *love x)  
_ = refl


-- Двусмысленное предложение:
-- Every human loves a human

s13 = s-vt (np-det every (cn-n Human)) (vt-n love) (np-det a/an (cn-n Human))

_ : (lookup ⟦s s13 ⟧ (# 0)) id ≡ (∀ (x : *Human) → Σ[ y ∈ *Human ] (x *love y)) 
_ = refl

_ : (lookup ⟦s s13 ⟧ (# 1)) id ≡ (Σ[ x ∈ *Human ] ∀(y : *Human) → (y *love x))
_ = refl



-- то же в пассиве
-- Every human is loved by a human
s18 = s-vtp (np-det every (cn-n Human)) (vt-n love) (np-det a/an (cn-n Human)) 

_ : (lookup ⟦s s18 ⟧ (# 0)) id ≡ (∀(x : *Human) → Σ[ y ∈ *Human ] (y *love x))
_ = refl

_ : (lookup ⟦s s18 ⟧ (# 1)) id ≡ (Σ[ y ∈ *Human ] ∀(x : *Human) → (y *love x))
_ = refl


-- Ralph believes ...

s19 = s-va (np-pn Ralph) (va-n believe) (s-nvp (np-det a/an (cn-n Human)) (vp-vi (vi-n is-spy)))

_ : (lookup ⟦s s19 ⟧ (# 0)) id ≡ (Σ[ x ∈ *Human ] (*Ralph believe[ _ ∈ *Human ] x *is-spy)) 
_ = refl

_ : (lookup ⟦s s19 ⟧ (# 1)) id ≡ (*Ralph believe[ x ∈ *Human ] x *is-spy)
_ = refl


s20 = s-va (np-det a/an (cn-n Human)) (va-n believe)
           (s-nvp (np-det a/an (cn-n Human)) (vp-vi (vi-n is-spy)))

_ : (lookup ⟦s s20 ⟧ (# 0)) id ≡ (Σ[ x ∈ *Human ] Σ[ h ∈ *Human ] (h believe[ _ ∈ *Human ] x *is-spy))
_ = refl

_ : (lookup ⟦s s20 ⟧ (# 1)) id ≡ (Σ[ h ∈ *Human ] (h believe[ x ∈ *Human ] x *is-spy))
_ = refl


-- John seeks a unicorn.

s21 = s-va (np-pn John) (va-n seek) (s-nvp (np-det a/an (cn-n Unicorn)) (vp-vi (vi-n exists)))

_ : (lookup ⟦s s21 ⟧ (# 0)) id ≡ (Σ[ x ∈ *Unicorn ] (*John seek[ _ ∈ *Unicorn ] x *exists))
_ = refl

_ : (lookup ⟦s s21 ⟧ (# 1)) id ≡ (*John seek[ x ∈ *Unicorn ] x *exists)
_ = refl

