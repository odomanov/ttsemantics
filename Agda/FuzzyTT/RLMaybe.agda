-- Adding Maybe to a Residuated Lattice

open import ResiduatedLattice

module RLMaybe {c} {ℓ₁} {ℓ₂} (la : ResiduatedLattice c ℓ₁ ℓ₂) where

open import Data.Maybe

MC = Maybe (Carrier la)
MC⊥ = just (⊥ la)
MC⊤ = just (⊤ la)

private
  _<*>_ : ∀ {l} {A B : Set l} → Maybe (A → B) → Maybe A → Maybe B
  mf <*> mx = mf >>= λ f → mx >>= λ x → just (f x)

infixl 4 _<*>_

-- applying a binary operation to the Maybe label
_⟪_⟫_ : MC → ((Carrier la) → (Carrier la) → (Carrier la)) → MC → MC
a ⟪ op ⟫ b = (just op) <*> a <*> b

-- the "or" version of ⟪∙⟫
-- _⟪_⟫⁺_ : MC → ((Carrier la) → (Carrier la) → (Carrier la)) → MC → MC
-- just v1 ⟪ op ⟫⁺ just v2 = just (op v1 v2)
-- nothing ⟪ op ⟫⁺ just v2 = just v2
-- just v1 ⟪ op ⟫⁺ nothing = just v1
-- nothing ⟪ op ⟫⁺ nothing = nothing

-- same for a unary operation
infixr 10 ⟪_⟫_

⟪_⟫_ : ((Carrier la) → (Carrier la)) → MC → MC
⟪ op ⟫ a = just op <*> a

infixl 10 _⟪⨂⟫_  -- _⟪⨁⟫⁺_

_⟪⨂⟫_ : MC → MC → MC
x ⟪⨂⟫ y = x ⟪ _⊗_ la ⟫ y 

_⟪⇒⟫_ : MC → MC → MC
x ⟪⇒⟫ y = x ⟪ _⇒_ la ⟫ y 

-- _⟪⨁⟫⁺_ : MC → MC → MC
-- x ⟪⨁⟫⁺ y = x ⟪ _⊕_ la ⟫⁺ y 

-- ⟪neg⟫ = ⟪ ⊘ la ⟫_

