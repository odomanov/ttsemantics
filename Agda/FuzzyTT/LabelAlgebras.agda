-- Using Labels for reasoning. Definitions of Label algebras
-- TODO: Prove 0≤v⊗ etc.

module LabelAlgebras where

open import Data.Bool
open import Data.Empty
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.String renaming (_++_ to _+++_)
open import Data.Unit
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import ArgPrelude

open import LabelAlgebra public
  renaming (⊤ to LA⊤; ⊥ to LA⊥; _∧_ to _LA∧_; _∨_ to _LA∨_)

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

postulate
  0≤vmean : ∀ n x y → 0.0 [≤] ((fromℕ n) [*] value y [+] value x) [/] (fromℕ (suc n)) ≡ true
  v≤1mean : ∀ n x y → ((fromℕ n) [*] value y [+] value x) [/] (fromℕ (suc n)) [≤] 1.0 ≡ true

-- adding n+1-th element (here ℕ denotes n)
FUmean : FUnit → FUnit → ℕ → FUnit
FUmean a acc n = record
  { value = (((fromℕ n) [*] value acc) [+] value a) [/] (fromℕ (suc n)) -- <n+1> = (n * <n> + a) / (n+1) 
  ; 0≤v = 0≤vmean n a acc 
  ; v≤1 = v≤1mean n a acc
  }

postulate
  0≤vadiff : ∀ a b → 0.0 [≤] (if value a [-] value b [≤] 0.0 then value b [-] value a else value a [-] value b) ≡ true
  v≤1adiff : ∀ a b → (if value a [-] value b [≤] 0.0 then value b [-] value a else value a [-] value b) [≤] 1.0 ≡ true

FUadiff : FUnit → FUnit → FUnit
FUadiff a b = record
  { value = if value a [-] value b [≤] 0.0 then value b [-] value a else value a [-] value b
  ; 0≤v = 0≤vadiff a b
  ; v≤1 = v≤1adiff a b
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
-- Trust Algebra

postulate
  0≤v⊗ : ∀ x y → 0.0 [≤] (value x) [*] (value y) ≡ true
  v≤1⊗ : ∀ x y → (value x) [*] (value y) [≤] 1.0 ≡ true

-- 0≤v⊗ : ∀ x y → 0.0 [≤] (value x) [*] (value y) ≡ true
-- 0≤v⊗ (mkFUnit value₁ 0≤v₁ v≤2) (mkFUnit value₂ 0≤v₂ v≤3) = {!0≤v₁!}

-- 0≤v⊗ : ∀ {x y} (v) → {_ : v ≡ (value x) [*] (value y)} → 0.0 [≤] v ≡ true
-- 0≤v⊗ {mkFUnit value₁ 0≤v₁ v≤2} {mkFUnit value₂ 0≤v₂ v≤3} v {p} = {!0≤v₁!}

Trust⊗ : FUnit → FUnit → FUnit
Trust⊗ a b = record
  { value = (value a) [*] (value b)
  ; 0≤v = 0≤v⊗ a b
  ; v≤1 = v≤1⊗ a b
  }

postulate
  0≤v⊕ : ∀ x y → 0.0 [≤] ((x [+] y) [-] (x [*] y)) ≡ true
  v≤1⊕ : ∀ x y → ((x [+] y) [-] (x [*] y)) [≤] 1.0 ≡ true

Trust⊕ : FUnit → FUnit → FUnit
Trust⊕ a b = record
  { value = (value a) [+] (value b) [-] ((value a) [*] (value b))
  ; 0≤v = 0≤v⊕ (value a) (value b)
  ; v≤1 = v≤1⊕ (value a) (value b)
  }

-- value⊖ : Float → Float → Float
-- value⊖ a b with 1.0 [=] a | 1.0 [=] b
-- ... | true  | false = 1.0
-- ... | false | _ with (a [<] b) ∨ not (a [=] b) | 1.0 [=] b
-- ...            | true | false = ((a [-] b) [/] (1.0 [-] b))
-- ...            | _    | _     = 0.0
-- value⊖ _ _ | _ | _ = 0.0

-- postulate
--   0≤v⊖ : ∀ x y → 0.0 [≤] (value⊖ x y) ≡ true
--   v≤1⊖ : ∀ x y → (value⊖ x y) [≤] 1.0 ≡ true

-- Trust⊖ : FUnit → FUnit → FUnit
-- Trust⊖ a b = record
--   { value = value⊖ (value a) (value b)
--   ; 0≤v = 0≤v⊖ (value a) (value b)
--   ; v≤1 = v≤1⊖ (value a) (value b)
--   }

Trust⊘ : FUnit → FUnit
Trust⊘ a = record
  { value = (value FU1) [-] (value a)
  ; 0≤v = 0≤v⊘ a
  ; v≤1 = v≤1⊘ a 
  }

Trust∧ : FUnit → FUnit → FUnit
Trust∧ a b = record
  { value = fmin (value a) (value b)
  ; 0≤v = min0≤v a b
  ; v≤1 = minv≤1 a b
  }

Trust∨ : FUnit → FUnit → FUnit
Trust∨ a b = record
  { value = fmax (value a) (value b)
  ; 0≤v = max0≤v a b
  ; v≤1 = maxv≤1 a b
  }

postulate
  Trust-isLabelAlgebra : IsLabelAlgebra
    FU= FU≤ Trust⊗ Trust⊕ -- Trust⊖
    Trust⊘ Trust∧ Trust∨ FUmean FUadiff FU1 FU0

Trust : LabelAlgebra _ _ _
Trust = record
  { Carrier = FUnit
  ; _≈_ = FU=
  ; _≤_ = FU≤
  ; _⊗_ = Trust⊗
  ; _⊕_ = Trust⊕
  -- ; _⊖_ = Trust⊖
  ; ⊘   = Trust⊘
  ; _∧_ = Trust∧
  ; _∨_ = Trust∨
  ; mean = FUmean
  ; adiff = FUadiff
  ; ⊤ = FU1
  ; ⊥ = FU0
  ; isLabelAlgebra = Trust-isLabelAlgebra
  ; doc = docFU
  }




-------------------------------------------------------
-- Preference Algebra

Pref⊗ : FUnit → FUnit → FUnit
Pref⊗ a b = record
  { value = fmin (value a) (value b)
  ; 0≤v = min0≤v a b 
  ; v≤1 = minv≤1 a b 
  }

postulate
  pref0≤v⊕ : ∀ x y → 0.0 [≤] (fmin (value x [+] value y) 1.0) ≡ true
  prefv≤1⊕ : ∀ x y → (fmin (value x [+] value y) 1.0) [≤] 1.0 ≡ true

Pref⊕ : FUnit → FUnit → FUnit
Pref⊕ a b = record
  { value = fmin (value a [+] value b) 1.0
  ; 0≤v = pref0≤v⊕ a b 
  ; v≤1 = prefv≤1⊕ a b 
  }

-- postulate
--   pref0≤v⊖ : ∀ x y → 0.0 [≤] (fmax ((value x) [-] (value y)) 0.0) ≡ true
--   prefv≤1⊖ : ∀ x y → (fmax ((value x) [-] (value y)) 0.0) [≤] 1.0 ≡ true

-- Pref⊖ : FUnit → FUnit → FUnit
-- Pref⊖ a b = record
--   { value = fmax ((value a) [-] (value b)) 0.0
--   ; 0≤v = pref0≤v⊖ a b 
--   ; v≤1 = prefv≤1⊖ a b 
--   }

Pref⊘ : FUnit → FUnit
Pref⊘ a = record
  { value = (value FU1) [-] (value a)
  ; 0≤v = 0≤v⊘ a 
  ; v≤1 = v≤1⊘ a 
  }

Pref∨ : FUnit → FUnit → FUnit
Pref∨ a b = record
  { value = fmax (value a) (value b)
  ; 0≤v = max0≤v a b
  ; v≤1 = maxv≤1 a b
  }

postulate
  Pref-isLabelAlgebra : IsLabelAlgebra
    FU= FU≤ Pref⊗ Pref⊕ -- Pref⊖
    Pref⊘ Pref⊗ Pref∨ FUmean FUadiff FU1 FU0

Pref : LabelAlgebra _ _ _
Pref = record
  { Carrier = FUnit
  ; _≈_ = FU=
  ; _≤_ = FU≤
  ; _⊗_ = Pref⊗
  ; _⊕_ = Pref⊕
  -- ; _⊖_ = Pref⊖
  ; ⊘   = Pref⊘
  ; _∧_ = Pref⊗
  ; _∨_ = Pref∨
  ; mean = FUmean
  ; adiff = FUadiff
  ; ⊤ = FU1
  ; ⊥ = FU0
  ; isLabelAlgebra = Pref-isLabelAlgebra
  ; doc = docFU
  }



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

postulate
  luk0≤v⊕ : ∀ x y → 0.0 [≤] (fmin (value x [+] value y) 1.0) ≡ true
  lukv≤1⊕ : ∀ x y → (fmin (value x [+] value y) 1.0) [≤] 1.0 ≡ true

Łuk⊕ : FUnit → FUnit → FUnit
Łuk⊕ a b = record
  { value = fmin (value a [+] value b) 1.0
  ; 0≤v = luk0≤v⊕ a b 
  ; v≤1 = lukv≤1⊕ a b 
  }

Łuk⊘ : FUnit → FUnit
Łuk⊘ a = record
  { value = (value FU1) [-] (value a)
  ; 0≤v = 0≤v⊘ a 
  ; v≤1 = v≤1⊘ a 
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
  Łuk-isLabelAlgebra : IsLabelAlgebra
    FU= FU≤ Łuk⊗ Łuk⊕ -- Łuk⊖
    Łuk⊘ Łuk∧ Łuk∨ FUmean FUadiff FU1 FU0

Łuk : LabelAlgebra _ _ _
Łuk = record
  { Carrier = FUnit
  ; _≈_ = FU=
  ; _≤_ = FU≤
  ; _⊗_ = Łuk⊗
  ; _⊕_ = Łuk⊕
  -- ; _⊖_ = Łuk⊖
  ; ⊘   = Łuk⊘
  ; _∧_ = Łuk∧
  ; _∨_ = Łuk∨
  ; mean = FUmean
  ; adiff = FUadiff
  ; ⊤ = FU1
  ; ⊥ = FU0
  ; isLabelAlgebra = Łuk-isLabelAlgebra
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

Göd⊕ : FUnit → FUnit → FUnit
Göd⊕ a b = record
  { value = fmax (value a) (value b)
  ; 0≤v = max0≤v a b 
  ; v≤1 = maxv≤1 a b 
  }

Göd⊘ : FUnit → FUnit
Göd⊘ = FUGneg
-- Göd⊘ a = record
--   { value = (value FU1) [-] (value a)
--   ; 0≤v = 0≤v⊘ a 
--   ; v≤1 = v≤1⊘ a 
--   }

Göd∧ = Göd⊗
Göd∨ = Göd⊕

postulate
  Gödel-isLabelAlgebra : IsLabelAlgebra
    FU= FU≤ Göd⊗ Göd⊕ -- Göd⊖
    Göd⊘ Göd∧ Göd∨ FUmean FUadiff FU1 FU0

Gödel : LabelAlgebra _ _ _
Gödel = record
  { Carrier = FUnit
  ; _≈_ = FU=
  ; _≤_ = FU≤
  ; _⊗_ = Göd⊗
  ; _⊕_ = Göd⊕
  -- ; _⊖_ = Göd⊖
  ; ⊘   = Göd⊘
  ; _∧_ = Göd∧
  ; _∨_ = Göd∨
  ; mean = FUmean
  ; adiff = FUadiff
  ; ⊤ = FU1
  ; ⊥ = FU0
  ; isLabelAlgebra = Gödel-isLabelAlgebra
  ; doc = docFU
  }


-------------------------------------------------------
-- Product t-norm (Shortliffe coefficients)

postulate
  prod0≤v⊗ : ∀ x y → 0.0 [≤] ((value x) [*] (value y)) ≡ true
  prodv≤1⊗ : ∀ x y → ((value x) [*] (value y)) [≤] 1.0 ≡ true
  prod0≤v⊕ : ∀ x y → 0.0 [≤] (value x) [+] (value y) [-] ((value x) [*] (value y)) ≡ true
  prodv≤1⊕ : ∀ x y → (value x) [+] (value y) [-] ((value x) [*] (value y)) [≤] 1.0 ≡ true

prod⊗ : FUnit → FUnit → FUnit
prod⊗ a b = record
  { value = (value a) [*] (value b)
  ; 0≤v = prod0≤v⊗ a b 
  ; v≤1 = prodv≤1⊗ a b 
  }

prod⊕ : FUnit → FUnit → FUnit
prod⊕ a b = record
  { value = (value a) [+] (value b) [-] ((value a) [*] (value b))
  ; 0≤v = prod0≤v⊕ a b 
  ; v≤1 = prodv≤1⊕ a b 
  }

prod⊘ : FUnit → FUnit
prod⊘ = FULneg
-- prod⊘ = FUGneg

prod∧ = FUmin
prod∨ = FUmax

postulate
  Product-isLabelAlgebra : IsLabelAlgebra
    FU= FU≤ prod⊗ prod⊕ -- prod⊖
    prod⊘ prod∧ prod∨ FUmean FUadiff FU1 FU0

Product : LabelAlgebra _ _ _
Product = record
  { Carrier = FUnit
  ; _≈_ = FU=
  ; _≤_ = FU≤
  ; _⊗_ = prod⊗
  ; _⊕_ = prod⊕
  -- ; _⊖_ = prod⊖
  ; ⊘   = prod⊘
  ; _∧_ = prod∧
  ; _∨_ = prod∨
  ; mean = FUmean
  ; adiff = FUadiff
  ; ⊤ = FU1
  ; ⊥ = FU0
  ; isLabelAlgebra = Product-isLabelAlgebra
  ; doc = docFU
  }


