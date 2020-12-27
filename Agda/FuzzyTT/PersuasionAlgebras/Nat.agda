-- Nat Persuasion Algebra

module PersuasionAlgebras.Nat  where

open import Level renaming (zero to lzero; suc to lsuc)
open import Algebra
open import Data.Nat 
open import Data.Nat.Properties
open import Data.Nat.Show renaming (show to ℕshow)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import PersuasionAlgebra hiding (_≤_) public
open import WLPretty

-------------------------------------------------------
-- PANat

docℕ : ℕ → Doc
docℕ n = text (ℕshow n)


PANat-isPersuasionAlgebra : IsPersuasionAlgebra _≡_ _≤_ _+_ zero
PANat-isPersuasionAlgebra = record { isPartialOrder = ≤-isPartialOrder
                                   ; isCommutativeMonoid = +-0-isCommutativeMonoid }

PANat : PersuasionAlgebra _ _ _
PANat = record
  { Carrier = ℕ
  ; _≈_ = _≡_
  ; _≤_ = _≤_
  ; _⊗_ = _+_
  ; ε = zero
  ; isPersuasionAlgebra = PANat-isPersuasionAlgebra
  ; doc = docℕ
  }


