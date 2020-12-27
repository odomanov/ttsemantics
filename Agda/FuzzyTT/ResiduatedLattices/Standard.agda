-- Some Residuated Lattices (derived from Persuasion algebras)
-- TODO: Prove 0≤v⊗ etc.
-- TODO: Prove that the algebras are residuated lattices

module ResiduatedLattices.Standard where

open import Level renaming (zero to lzero; suc to lsuc)
open import Algebra
open import Data.Bool
open import Data.Empty
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Float
open import ResiduatedLattice public
open import PersuasionAlgebras.Standard



-------------------------------------------------------
-- Łukasiewicz Algebra

postulate
  luk0≤v⇒ : ∀ x y → 0.0 [≤] (fmin 1.0 (1.0 [-] (value x) [+] (value y))) ≡ true
  lukv≤1⇒ : ∀ x y → (fmin 1.0 (1.0 [-] (value x) [+] (value y))) [≤] 1.0 ≡ true

Łuk⇒ : FUnit → FUnit → FUnit
Łuk⇒ a b = record
  { value = fmin 1.0 (1.0 [-] (value a) [+] (value b))
  ; 0≤v = luk0≤v⇒ a b 
  ; v≤1 = lukv≤1⇒ a b 
  }

Łuk∧ : FUnit → FUnit → FUnit
Łuk∧ a b = record
  { value = fmin (value a) (value b)
  ; 0≤v = min0≤v a b
  ; v≤1 = minv≤1 a b
  }

Łuk∨ : FUnit → FUnit → FUnit
Łuk∨ a b = record
  { value = fmax (value a) (value b)
  ; 0≤v = max0≤v a b
  ; v≤1 = maxv≤1 a b
  }

postulate
  Łuk-isResiduatedLattice : IsResiduatedLattice
    FU= FU≤ Łuk⊗ Łuk⇒ Łuk∧ Łuk∨ FU1 FU0

ŁukRL : ResiduatedLattice _ _ _
ŁukRL = record
  { persuasionAlgebra  = Łuk
  ; _⇒_ = Łuk⇒
  ; _∧_ = Łuk∧
  ; _∨_ = Łuk∨
  ; ⊤ = FU1
  ; ⊥ = FU0
  ; isResiduatedLattice = Łuk-isResiduatedLattice
  ; doc = docFU
  }


-------------------------------------------------------
-- Gödel t-norm

postulate
  god0≤v⇒ : ∀ x y → 0.0 [≤] (if (value x) [≤] (value y) then 1.0 else (value y)) ≡ true
  godv≤1⇒ : ∀ x y → (if (value x) [≤] (value y) then 1.0 else (value y)) [≤] 1.0 ≡ true

Göd⇒ : FUnit → FUnit → FUnit
Göd⇒ a b = record
  { value = if (value a) [≤] (value b) then 1.0 else (value b)
  ; 0≤v = god0≤v⇒ a b 
  ; v≤1 = godv≤1⇒ a b 
  }

Göd∨ : FUnit → FUnit → FUnit
Göd∨ a b = record
  { value = fmax (value a) (value b)
  ; 0≤v = max0≤v a b 
  ; v≤1 = maxv≤1 a b 
  }

Göd∧ = Göd⊗

postulate
  Gödel-isResiduatedLattice : IsResiduatedLattice
    FU= FU≤ Göd⊗ Göd⇒ Göd∧ Göd∨ FU1 FU0

GödelRL : ResiduatedLattice _ _ _
GödelRL = record
  { persuasionAlgebra = Gödel
  ; _⇒_ = Göd⇒
  ; _∧_ = Göd∧
  ; _∨_ = Göd∨
  ; ⊤ = FU1
  ; ⊥ = FU0
  ; isResiduatedLattice = Gödel-isResiduatedLattice
  ; doc = docFU
  }


-------------------------------------------------------
-- Product t-norm (Shortliffe coefficients)

postulate
  prod0≤v⇒ : ∀ x y → 0.0 [≤] (if (value x) [≤] (value y) then 1.0 else (value y) [/] (value x)) ≡ true
  prodv≤1⇒ : ∀ x y → (if (value x) [≤] (value y) then 1.0 else (value y) [/] (value x)) [≤] 1.0 ≡ true

prod⇒ : FUnit → FUnit → FUnit
prod⇒ a b = record
  { value = if (value a) [≤] (value b) then 1.0 else (value b) [/] (value a)
  ; 0≤v = prod0≤v⇒ a b 
  ; v≤1 = prodv≤1⇒ a b 
  }

prod∧ = FUmin
prod∨ = FUmax

postulate
  Product-isResiduatedLattice : IsResiduatedLattice
    FU= FU≤ prod⊗ prod⇒ prod∧ prod∨ FU1 FU0

ProductRL : ResiduatedLattice _ _ _
ProductRL = record
  { persuasionAlgebra = Product
  ; _⇒_ = prod⇒
  ; _∧_ = prod∧
  ; _∨_ = prod∨
  ; ⊤ = FU1
  ; ⊥ = FU0
  ; isResiduatedLattice = Product-isResiduatedLattice
  ; doc = docFU
  }


