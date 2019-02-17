module KripkeModel where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.String using (String)
open import Data.List using (List; []; _∷_) 
open import Agda.Builtin.Nat
open import Data.Product using (_×_)
open import Relation.Nullary using (¬_)
open import Data.Empty


-- Atomic propositions
data Atomic : Set where
  at_ : String → Atomic

-- Agents
data Agent : Set where
  ag_ : String → Agent

infix 7 ⟪_⟫
infix 6 ~_
infix 6 K₍_₎_
infix 5 _∧_

-- Formulas
data Frm : Set where
  ⟪_⟫   : Atomic -> Frm
  ~_   : Frm -> Frm
  _∧_  : Frm -> Frm -> Frm
  K₍_₎_ : Agent -> Frm -> Frm
  f⊥ : Frm

f⊤ : Frm
f⊤ = ~ f⊥

infix 5 _∨_
infix 5 _⇒_
infix 6 M₍_₎_

_∨_ : Frm -> Frm -> Frm
_∨_ a b = ~ (~ a ∧ ~ b)

_⇒_ : Frm -> Frm -> Frm
_⇒_ a b = ~ a ∨ b

M₍_₎_ : Agent -> Frm -> Frm
M₍_₎_ a φ = ~ (K₍ a ₎ (~ φ))


-- everyone in A knows
E : List Agent -> Frm -> Frm
E [] _ = f⊤
E (a ∷ Agents) φ = (KK a) ∧ (E Agents φ) where
  KK : Agent -> Frm
  KK a = K₍ a ₎ φ


-- Length
∣_∣ : Frm -> Nat
∣_∣ ⟪ _ ⟫      = 1
∣_∣ (~ φ)     = ∣ φ ∣ + 1
∣_∣ (φ ∧ ψ)   = ∣ φ ∣ + ∣ ψ ∣ + 1
∣_∣ (K₍ _ ₎ φ) = ∣ φ ∣ + 1
∣_∣ ⊥         = 1



-- Modal depth
-- <to do>



--  Semantics

-- Kripke Model
record KModel : Set1 where
  field
    World : Set                                -- possible worlds
    Racc₍_₎ : Agent → World → World → Set       -- accessibility for all agents
    Val : World → Atomic → Set                 -- valuation

module Semantics (km : KModel) where

  open KModel km

  infix 3 _⊨_
  
  -- Выполнимость в модели
  _⊨_ : World → Frm → Set
  s ⊨ ⟪ p ⟫      = Val s p 
  s ⊨ (φ ∧ ψ)    = (s ⊨ φ) × (s ⊨ ψ) 
  s ⊨ (~ φ)      = ¬ (s ⊨ φ)
  s ⊨ (K₍ a ₎ φ)  = ∀ t → (Racc₍ a ₎ s t) → (t ⊨ φ)
  s ⊨ f⊥         = ⊥
