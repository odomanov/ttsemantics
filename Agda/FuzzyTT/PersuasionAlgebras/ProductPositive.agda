-- Some Persuasion Algebras
-- TODO: Prove 0≤v⊗ etc.
-- TODO: Prove that the algebras are persuasion algebras

module PersuasionAlgebras.ProductPositive where

open import Level renaming (zero to lzero; suc to lsuc)
open import Algebra
open import Data.Bool
open import Data.Empty
open import Data.Maybe
open import Data.Nat as ℕ
open import Data.Nat.Show renaming (show to ℕshow)
open import Data.Product
open import Data.String renaming (_++_ to _+++_)
open import Data.Unit
open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Float

open import PersuasionAlgebra public

-- Float interval [0..]
record FPositive : Set where
  constructor mkFPositive
  field
    value : Float
    0≤v   : (0.0 [≤] value) ≡ true

open FPositive public

V : (x : Float) → {p1 : 0.0 [≤] x ≡ true} → FPositive
V x {p1} = record { value = x; 0≤v = p1 }

FPositive0 : FPositive
FPositive0 = record { value = 0.0; 0≤v = refl }

FPositive1 : FPositive
FPositive1 = record { value = 1.0; 0≤v = refl }

FPositive= : FPositive → FPositive → Set
FPositive= a b = value a ≡ value b

FPositive< : FPositive → FPositive → Set
FPositive< a b = if (value a) [<] (value b) then ⊤ else ⊥ 

FPositive≤ : FPositive → FPositive → Set
FPositive≤ a b = if (value a) [≤] (value b) then ⊤ else ⊥ 


FPositive=-refl : Reflexive FPositive=
FPositive=-refl = refl

FPositive=-sym : Symmetric FPositive=
FPositive=-sym refl = refl

FPositive=-trans : Transitive FPositive=
FPositive=-trans refl eq = eq


fmin : Float → Float → Float
fmin x y = if x [<] y then x else y 

fmax : Float → Float → Float
fmax x y = if x [<] y then y else x 

min0≤v : ∀ x y → (0.0 [≤] (fmin (value x) (value y)) ≡ true)
min0≤v x y with (value x) [<] (value y)
min0≤v (mkFPositive _ 0≤v₁) y | true = 0≤v₁
min0≤v x (mkFPositive _ 0≤v₁) | false = 0≤v₁

max0≤v : ∀ x y → (0.0 [≤] (fmax (value x) (value y)) ≡ true)
max0≤v x y with (value x) [<] (value y)
max0≤v x (mkFPositive _ 0≤v₁) | true = 0≤v₁
max0≤v (mkFPositive _ 0≤v₁) y | false = 0≤v₁

FPositivemin : FPositive → FPositive → FPositive 
FPositivemin a b = record
  { value = fmin (value a) (value b) 
  ; 0≤v = min0≤v a b 
  }

FPositivemax : FPositive → FPositive → FPositive 
FPositivemax a b = record
  { value = fmax (value a) (value b) 
  ; 0≤v = max0≤v a b 
  }


docFPositive : FPositive → Doc
docFPositive (mkFPositive x _) = docFloatRounded 4 x 




-------------------------------------------------------
-- ProductPositive

postulate
  prod0≤v⊗ : ∀ x y → 0.0 [≤] ((value x) [*] (value y)) ≡ true

prod⊗ : FPositive → FPositive → FPositive
prod⊗ a b = record
  { value = (value a) [*] (value b)
  ; 0≤v = prod0≤v⊗ a b 
  }

postulate
  ProductPositive-isPersuasionAlgebra : IsPersuasionAlgebra FPositive= FPositive≤ prod⊗ FPositive1 

ProductPositive : PersuasionAlgebra _ _ _
ProductPositive = record
  { Carrier = FPositive
  ; _≈_ = FPositive=
  ; _≤_ = FPositive≤
  ; _⊗_ = prod⊗
  ; ε = FPositive1
  ; isPersuasionAlgebra = ProductPositive-isPersuasionAlgebra
  ; doc = docFPositive
  }


