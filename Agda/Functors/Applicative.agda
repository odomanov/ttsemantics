{-# OPTIONS --cumulativity #-}
module _ where

open import Data.Empty
open import Data.Maybe
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality
open import Level
1ℓ = suc 0ℓ
2ℓ = suc 1ℓ

record RawApplicative {ℓ} (F : Set ℓ → Set ℓ) : Set (suc ℓ) where
  infixl 4 _<*>_ _<$>_
  field
    pure  : ∀{A : Set ℓ} → A → F A
    _<*>_ : ∀{A B : Set ℓ} → F (A → B) → F A → F B

  _<$>_ : ∀{A B : Set ℓ} → (A → B) → F A → F B
  f <$> fa = pure f <*> fa

data ВозмМир : Set where
  w₁ w₂ : ВозмМир
  
F : ∀{a} → Set a → Set a
F A = ВозмМир → A

applicative : ∀{ℓ} → RawApplicative {ℓ} F
applicative = record { pure  = λ x r → x
                     ; _<*>_ = λ f fa r → (f r) (fa r)
                     }

module Ex1 where

  open RawApplicative {0ℓ} applicative
  
  data Страна : Set where
    Россия : Страна

  data Город : Set where
    Москва Новосибирск : Город 

  страна : F Страна
  страна w₁ = Россия
  страна w₂ = Россия
  
  столица : F (Страна → Город)
  столица w₁ = λ { Россия → Москва }
  столица w₂ = λ { Россия → Новосибирск }
  
  s : F Город
  s = столица <*> страна
  
  _ : s w₁ ≡ Москва
  _ = refl
  
  _ : s w₂ ≡ Новосибирск
  _ = refl
  

-- зависимый тип 
module Ex2 where

  open RawApplicative {1ℓ} applicative
  
  data Страна : Set where
    Россия : Страна

  data Город : Set where
    Москва Новосибирск : Город 

  страна : F Страна
  страна w₁ = Россия
  страна w₂ = Россия

  data Столица₁ : Страна → Set where
    Москва : Столица₁ Россия
    
  data Столица₂ : Страна → Set where
    Новосибирск : Столица₂ Россия
    
  столица : F (Страна → Set)
  столица w₁ = Столица₁
  столица w₂ = Столица₂

  s : F _
  s = столица <*> страна
  
  _ : s w₁ ≡ Столица₁ Россия 
  _ = refl

  _ : s w₁
  _ = Москва

  _ : s w₂
  _ = Новосибирск


  -- глагол как зависимый тип
  data Human : Set where
    Mary Naomi Alex : Human

  runner : F Human
  runner w₁ = Mary
  runner w₂ = Alex 

  -- в разных мирах разные пропозиции, т.е. типы
  data run₁ : Human → Set where
    mr : run₁ Mary

  data run₂ : Human → Set where
    ar : run₂ Alex

  run : F (Human → Set)
  run w₁ = run₁
  run w₂ = run₂

  hr : F _ 
  hr = run <*> runner

  _ : hr w₁
  _ = mr
  
  _ : hr w₂
  _ = ar
  

  -- местоимения в контексте
  she : F Human
  she w₁ = Mary
  she w₂ = Naomi

  she-runs : F _
  she-runs = run <*> she 

  _ : she-runs w₁
  _ = mr

  -- her father
  father₁ : Human → Maybe Human
  father₁ Mary = just Alex
  father₁ _ = nothing

  father₂ : Human → Maybe Human
  father₂ Naomi = just Alex
  father₂ _ = nothing

  father : F (Human → Maybe Human)
  father w₁ = father₁
  father w₂ = father₂

  her-father : F _
  her-father = father <*> she 

  _ : her-father w₁ ≡ just Alex
  _ = refl

  _ : her-father w₂ ≡ just Alex
  _ = refl

  runm : F (Maybe Human → Set)
  runm w₁ (just x) = run₁ x
  runm w₁ nothing = ⊥
  runm w₂ (just x) = run₂ x
  runm w₂ nothing = ⊥

  her-father-runs : F _
  her-father-runs = runm <*> (father <*> she)

  _ : her-father-runs w₂
  _ = ar


  -- варианты определений
  
  postulate father' : Human → Human

  her-father' : F _
  her-father' = pure father' <*> she
  
  her-father'' : F _
  her-father'' = father' <$> she

  postulate run' : Maybe Human → Set
  
  her-father-runs' : F _
  her-father-runs' = run' <$> (father <*> she)
  
