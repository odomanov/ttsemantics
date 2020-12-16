-- Some Residuated Lattices
-- TODO: Prove 0≤v⊗ etc.

module _  where

open import Data.Bool
open import Data.Empty
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.String renaming (_++_ to _+++_)
open import Data.Unit
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Float

open import ResiduatedLattice public
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

Łuk : ResiduatedLattice _ _ _
Łuk = record
  { Carrier = FUnit
  ; _≈_ = FU=
  ; _≤_ = FU≤
  ; _⊗_ = Łuk⊗
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

Göd⊗ : FUnit → FUnit → FUnit
Göd⊗ a b = record
  { value = fmin (value a) (value b)
  ; 0≤v = min0≤v a b 
  ; v≤1 = minv≤1 a b 
  }

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

Gödel : ResiduatedLattice _ _ _
Gödel = record
  { Carrier = FUnit
  ; _≈_ = FU=
  ; _≤_ = FU≤
  ; _⊗_ = Göd⊗
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
  prod0≤v⊗ : ∀ x y → 0.0 [≤] ((value x) [*] (value y)) ≡ true
  prodv≤1⊗ : ∀ x y → ((value x) [*] (value y)) [≤] 1.0 ≡ true

prod⊗ : FUnit → FUnit → FUnit
prod⊗ a b = record
  { value = (value a) [*] (value b)
  ; 0≤v = prod0≤v⊗ a b 
  ; v≤1 = prodv≤1⊗ a b 
  }

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

Product : ResiduatedLattice _ _ _
Product = record
  { Carrier = FUnit
  ; _≈_ = FU=
  ; _≤_ = FU≤
  ; _⊗_ = prod⊗
  ; _⇒_ = prod⇒
  ; _∧_ = prod∧
  ; _∨_ = prod∨
  ; ⊤ = FU1
  ; ⊥ = FU0
  ; isResiduatedLattice = Product-isResiduatedLattice
  ; doc = docFU
  }


