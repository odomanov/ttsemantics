-- Some Persuasion Algebras
-- TODO: Prove 0≤v⊗ etc.
-- TODO: Prove that the algebras are persuasion algebras

module PersuasionAlgebras.Standard where

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

-- Float interval [0..1]
record FUnit : Set where
  constructor mkFUnit
  field
    value : Float
    0≤v   : (0.0 [≤] value) ≡ true
    v≤1   : (value [≤] 1.0) ≡ true

open FUnit public

V : (x : Float) → {p1 : 0.0 [≤] x ≡ true} → {p2 : x [≤] 1.0 ≡ true} → FUnit
V x {p1} {p2} = record { value = x; 0≤v = p1; v≤1 = p2 }

FU0 : FUnit
FU0 = record { value = 0.0; 0≤v = refl; v≤1 = refl }

FU1 : FUnit
FU1 = record { value = 1.0; 0≤v = refl; v≤1 = refl }

FU= : FUnit → FUnit → Set
FU= a b = value a ≡ value b

FU< : FUnit → FUnit → Set
FU< a b = if (value a) [<] (value b) then ⊤ else ⊥ 

FU≤ : FUnit → FUnit → Set
FU≤ a b = if (value a) [≤] (value b) then ⊤ else ⊥ 


FU=-refl : Reflexive FU=
FU=-refl = refl

FU=-sym : Symmetric FU=
FU=-sym refl = refl

FU=-trans : Transitive FU=
FU=-trans refl eq = eq


fmin : Float → Float → Float
fmin x y = if x [<] y then x else y 

fmax : Float → Float → Float
fmax x y = if x [<] y then y else x 

private
  negg : Float → Float
  negg 0.0 = 1.0
  negg _ = 0.0

postulate
  0≤vgneg : ∀ a → 0.0 [≤] (negg a) ≡ true
  v≤1gneg : ∀ a → (negg a) [≤] 1.0 ≡ true

-- Gödel negation
FUGneg : FUnit → FUnit
FUGneg a = record
  { value = negg (value a)
  ; 0≤v = 0≤vgneg (value a)
  ; v≤1 = v≤1gneg (value a)
  }

postulate
  0≤v⊘ : ∀ x → 0.0 [≤] (value FU1) [-] value x ≡ true
  v≤1⊘ : ∀ x → (value FU1) [-] value x [≤] 1.0 ≡ true

-- Łukasiewicz negation
FULneg : FUnit → FUnit
FULneg a = record
  { value = (value FU1) [-] (value a)
  ; 0≤v = 0≤v⊘ a 
  ; v≤1 = v≤1⊘ a 
  }

min0≤v : ∀ x y → (0.0 [≤] (fmin (value x) (value y)) ≡ true)
min0≤v x y with (value x) [<] (value y)
min0≤v (mkFUnit _ 0≤v₁ _) y | true = 0≤v₁
min0≤v x (mkFUnit _ 0≤v₁ _) | false = 0≤v₁

minv≤1 : ∀ x y → (fmin (value x) (value y)) [≤] 1.0 ≡ true
minv≤1 x y with (value x) [<] (value y)
minv≤1 (mkFUnit _ _ v≤2) y | true = v≤2
minv≤1 x (mkFUnit _ _ v≤2) | false = v≤2

max0≤v : ∀ x y → (0.0 [≤] (fmax (value x) (value y)) ≡ true)
max0≤v x y with (value x) [<] (value y)
max0≤v x (mkFUnit _ 0≤v₁ _) | true = 0≤v₁
max0≤v (mkFUnit _ 0≤v₁ _) y | false = 0≤v₁

maxv≤1 : ∀ x y → (fmax (value x) (value y)) [≤] 1.0 ≡ true
maxv≤1 x y with (value x) [<] (value y)
maxv≤1 x (mkFUnit _ _ v≤2) | true = v≤2
maxv≤1 (mkFUnit _ _ v≤2) y | false = v≤2

FUmin : FUnit → FUnit → FUnit 
FUmin a b = record
  { value = fmin (value a) (value b) 
  ; 0≤v = min0≤v a b 
  ; v≤1 = minv≤1 a b 
  }

FUmax : FUnit → FUnit → FUnit 
FUmax a b = record
  { value = fmax (value a) (value b) 
  ; 0≤v = max0≤v a b 
  ; v≤1 = maxv≤1 a b 
  }


docFU : FUnit → Doc
docFU (mkFUnit x _ _) = docFloatRounded 4 x 




-------------------------------------------------------
-- Łukasiewicz Algebra

postulate
  luk0≤v⊗ : ∀ x y → 0.0 [≤] (fmax 0.0 ((value x) [+] (value y) [-] 1.0)) ≡ true
  lukv≤1⊗ : ∀ x y → (fmax 0.0 ((value x) [+] (value y) [-] 1.0)) [≤] 1.0 ≡ true

Łuk⊗ : FUnit → FUnit → FUnit
Łuk⊗ a b = record
  { value = fmax 0.0 ((value a) [+] (value b) [-] 1.0)
  ; 0≤v = luk0≤v⊗ a b 
  ; v≤1 = lukv≤1⊗ a b 
  }

Łuk-cong : Congruent₂ FU= Łuk⊗
Łuk-cong refl refl = refl

postulate
  Łuk1+v=v : ∀ x → FU= (Łuk⊗ FU1 x) x
  Łukv+1=v : ∀ x → FU= (Łuk⊗ x FU1) x 


-- TODO:

-- Łuk-assoc : Associative FU= Łuk⊗
-- Łuk-assoc (mkFUnit x px1 px2) y z = {!refl!} 
Łuk-identity : Identity FU= FU1 Łuk⊗
Łuk-identity = L , R
  where
  L : LeftIdentity FU= FU1 Łuk⊗
  L x = Łuk1+v=v x
  R : RightIdentity FU= FU1 Łuk⊗
  R x = Łukv+1=v x
-- Łuk-comm : Commutative FU= Łuk⊗
-- Łuk-comm (mkFUnit value₁ 0≤v₁ v≤2) (mkFUnit value₂ 0≤v₂ v≤3) = {!refl!}

-- Łuk-isCommutativeMonoid : IsCommutativeMonoid FU= Łuk⊗ FU1
-- Łuk-isCommutativeMonoid = record
--                  { isMonoid = record
--                    { isSemigroup = record
--                      { isMagma = record
--                        { isEquivalence = record
--                          { refl = refl ; sym = FU=-sym ; trans = FU=-trans }
--                        ; ∙-cong = {!!}
--                        }
--                      ; assoc = {!!}
--                      }
--                    ; identity = {!!}
--                    }
--                  ; comm = {!!}
--                  }  

postulate
  Łuk-isPersuasionAlgebra : IsPersuasionAlgebra FU= FU≤ Łuk⊗ FU1

Łuk : PersuasionAlgebra _ _ _
Łuk = record
  { Carrier = FUnit
  ; _≈_ = FU=
  ; _≤_ = FU≤
  ; _⊗_ = Łuk⊗
  ; ε = FU1
  ; isPersuasionAlgebra = Łuk-isPersuasionAlgebra
  ; doc = docFU
  }


-------------------------------------------------------
-- Gödel t-norm

Göd⊗ : FUnit → FUnit → FUnit
Göd⊗ a b = record
  { value = fmin (value a) (value b)
  ; 0≤v = min0≤v a b 
  ; v≤1 = minv≤1 a b 
  }

postulate
  Gödel-isPersuasionAlgebra : IsPersuasionAlgebra FU= FU≤ Göd⊗ FU1

Gödel : PersuasionAlgebra _ _ _
Gödel = record
  { Carrier = FUnit
  ; _≈_ = FU=
  ; _≤_ = FU≤
  ; _⊗_ = Göd⊗
  ; ε = FU1
  ; isPersuasionAlgebra = Gödel-isPersuasionAlgebra
  ; doc = docFU
  }


-------------------------------------------------------
-- Product t-norm (Shortliffe coefficients)

postulate
  prod0≤v⊗ : ∀ x y → 0.0 [≤] ((value x) [*] (value y)) ≡ true
  prodv≤1⊗ : ∀ x y → ((value x) [*] (value y)) [≤] 1.0 ≡ true

prod⊗ : FUnit → FUnit → FUnit
prod⊗ a b = record
  { value = (value a) [*] (value b)
  ; 0≤v = prod0≤v⊗ a b 
  ; v≤1 = prodv≤1⊗ a b 
  }

postulate
  Product-isPersuasionAlgebra : IsPersuasionAlgebra FU= FU≤ prod⊗ FU1 

Product : PersuasionAlgebra _ _ _
Product = record
  { Carrier = FUnit
  ; _≈_ = FU=
  ; _≤_ = FU≤
  ; _⊗_ = prod⊗
  ; ε = FU1
  ; isPersuasionAlgebra = Product-isPersuasionAlgebra
  ; doc = docFU
  }


