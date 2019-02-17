module Ralph where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Product using (_×_; proj₁; proj₂) 
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Relation.Nullary using (¬_)


postulate
  man : Set
  spy : man → Set


-- Ralph's beliefs
record ΓR : Set where
  field
    xh : man        -- человек в шляпе
    xb : man        -- человек на пляже
    sh : spy xh
    sb : ¬ (spy xb)

open ΓR

-- Ральф верит, что человек в шляпе --- шпион
_ : ∀ (γ : ΓR) → spy (xh γ)
_ = sh

-- Ральф верит, что человек на пляже --- не шпион
_ : ∀ (γ : ΓR) → ¬ spy (xb γ)
_ = sb


-- Ральф верит, что существует шпион
_ : ∀ (γ : ΓR) → Σ[ m ∈ man ] spy m
_ = λ γ → xh γ , sh γ

-- Ральф верит, что существует НЕ шпион
_ : ∀ (γ : ΓR) → Σ[ m ∈ man ] ¬ spy m
_ = λ γ → xb γ , sb γ



-- instance of ΓR

postulate
  o mh mb : man     -- o = Ortcutt
  ssh : spy mh
  ssb : ¬ spy mb

γr = record {xh = mh; xb = mb; sh = ssh; sb = ssb }

_ : mh ≡ xh γr
_ = refl

open ΓR γr



----------------------------------------------------------------------------
-- Counterpart relation  ---------------------------------------------------

infix 6 _≈_

data _≈_ : man → (ΓR → man) → Set where
  coh : o ≈ xh
  cob : o ≈ xb

-- тип близнецов для человека m
CR : man → Set
CR m = Σ[ x ∈ (ΓR → man)] m ≈ x


-- существует близнец Орткута, равный xh (т.е. xh есть близнец Орткута)

_ : Σ[ x ∈ (CR o) ] x ≡ (xh , coh)
_ = (xh , coh) , refl

_ : Σ[ x ∈ (CR o) ] proj₁ x ≡ xh 
_ = (xh , coh) , refl


-- существует человек, для которого есть близнец в контексте Ральфа,
-- равный xh (т.е. для которого xh является близнецом в контекте Ральфа)

_ : Σ[ m ∈ man ] Σ[ x ∈ (CR m) ] proj₁ x ≡ xh
_ = o , ((xh , coh) , refl)

-- существует человек, для которого есть близнец в контексте Ральфа

_ : Σ[ x ∈ (CR o) ] (Σ[ m ∈ (ΓR → man) ] proj₁ x ≡ m )
_ = (xh , coh) , (xh , refl)

-- то же, но с другим доказательством
_ : Σ[ x ∈ (CR o) ] (Σ[ m ∈ (ΓR → man) ] proj₁ x ≡ m )
_ = (xb , cob) , (xb , refl)

-- Существует человек, близнец которого --- шпион (для Ральфа)

-- для любого γ
_ : ∀ (γ : ΓR) → Σ[ m ∈ man ] (Σ[ x ∈ (CR m) ] spy ((proj₁ x) γ))
_ = λ γ → o , ((xh , coh) , (sh γ))

-- для γr
_ : Σ[ m ∈ man ] (Σ[ x ∈ (CR m) ] spy ((proj₁ x) γr) )
_ = o , ((xh , coh) , ssh)

-- Существует человек, близнец которого --- НЕ шпион (для Ральфа)

-- для любого γ
_ : ∀ (γ : ΓR) → Σ[ m ∈ man ] (Σ[ x ∈ (CR m) ] ¬ spy ((proj₁ x) γ))
_ = λ γ → o , ((xb , cob) , (sb γ))

-- для γr
_ : Σ[ m ∈ man ] (Σ[ x ∈ (CR m) ] ¬ spy ((proj₁ x) γr))
_ = o , ((xb , cob) , ssb)



