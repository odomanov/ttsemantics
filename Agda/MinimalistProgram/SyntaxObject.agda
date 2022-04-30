-- Syntax Object as DAG

module _ where

open import Data.Bool
open import Data.Fin as 𝔽 
open import Data.List hiding ([_])
open import Data.Maybe
open import Data.Nat as ℕ
open import Data.Nat.Properties using (n≤1+n; ≤-step)
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary using (yes; no)

open import Feature public


--=== Label ===--

record Label : Set where
  constructor mkLabel   
  field
    F  : FList
    uF : FList

pattern _∙_ x y = just (mkLabel x y)

infix 4 mkLabel _∙_

instance
  EqLabel : Eq Label Label
  _==_ {{EqLabel}} (mkLabel F₁ uF₁) (mkLabel F₂ uF₂) = F₁ == F₂ ∧ uF₁ == uF₂

EI→Label : EnumItem → Label
EI→Label (lex (mkLI F uF)) = mkLabel F uF
EI→Label (fun (mkFC F uF)) = mkLabel F uF

-- the label of the head
E→Label : ∀ {n} → Enum n → Label
E→Label (li ⊣) = EI→Label li
E→Label (li ∷ _) = EI→Label li



--=== Syntax Stage and Syntax Object ===--

-- Syntax object
data SO : Set where
  ⟦_⊣⟧    : ∀ {n} → Enum n → SO                      -- selected (from Enum)
  ⟦_-_-_⟧ : Maybe Label → SO → SO → SO               -- merge

-- infix 7 ⟦_⊣⟧
infixr 6 ⟦_-_-_⟧

instance
  EqSO : Eq SO SO
  _==_ ⦃ EqSO ⦄ ⟦ x1 ⊣⟧ ⟦ x2 ⊣⟧ = x1 == x2 
  _==_ ⦃ EqSO ⦄ ⟦ x1 - s11 - s12 ⟧ ⟦ x2 - s21 - s22 ⟧ = s11 == s21 ∧ x1 == x2 ∧ s21 == s22
  _==_ ⦃ EqSO ⦄ _ _ = false



--==≡≡  Syntax stage; n is the size of Stage (the number of objects; Nodes + 1)  ≡≡==--

infixr 6 _&_

data Node : ℕ → Set where
  Select : ∀ {n m} → Enum m → Node n        
  Merge  : ∀ {n} → Fin (suc n) → Fin (suc n) → Node (suc n)  -- both External and Internal Merge 
  Adjoin : ∀ {n} → Fin (suc n) → Fin (suc n) → Node (suc n)

data Stage : ℕ → Set where
  ∅   : Stage zero                                  -- empty Stage
  _&_ : ∀ {n} → Node n → Stage n → Stage (suc n)    -- add an object to the Stage

instance
  EqNode : ∀ {n m} → Eq (Node n) (Node m)
  _==_ {{EqNode {n} {m}}} (Select x1)      (Select x2)      = n == m ∧ x1 == x2 
  _==_ {{EqNode {n} {m}}} (Merge  i1 j1) (Merge  i2 j2) = n == m ∧ i1 == i2 ∧ j1 == j2
  _==_ {{EqNode {n} {m}}} (Adjoin i1 j1) (Adjoin i2 j2) = n == m ∧ i1 == i2 ∧ j1 == j2 
  _==_ {{EqNode}} _ _ = false
  
  EqStage : ∀ {n m} → Eq (Stage n) (Stage m)
  _==_ ⦃ EqStage ⦄ ∅ ∅ = true
  _==_ ⦃ EqStage ⦄ (x1 & s1) (x2 & s2) = x1 == x2 ∧ s1 == s2
  _==_ ⦃ EqStage ⦄ _ _ = false


-- the label of SO
lbl : SO → Maybe Label
lbl ⟦ x ⊣⟧ = just (E→Label x)
lbl ⟦ x - _ - _ ⟧ = x

-- maximal projection for Labels
_is-maxⁿ : Label → Bool
_is-maxⁿ (mkLabel _ []) = true
_is-maxⁿ _ = false

-- maximal projection
_is-max : SO → Bool
_is-max s = is-maxⁿ-Maybe (lbl s)
  where
  is-maxⁿ-Maybe : Maybe Label → Bool
  is-maxⁿ-Maybe (_ ∙ []) = true
  is-maxⁿ-Maybe _ = false

-- minimal projection
_is-min : SO → Bool
⟦ _ ⊣⟧ is-min = true
_ is-min = false

-- unchecked feature exists
{-# TERMINATING #-}
feature-exists? : Feature → Label → Bool
feature-exists? _ (mkLabel _ []) = false
feature-exists? f (mkLabel F (uf ∷ ufs)) with f == uf
... | true = true
... | false = feature-exists? f (mkLabel F ufs)

-- remove the first matching feature from the list
remove : {A : Set} → List A → A → {{Eq A A}} → List A
remove l a = removeAcc l a []
  where
  removeAcc : {A : Set} → List A → A → (acc : List A) → {{Eq A A}} → List A
  removeAcc [] _ _ = []
  removeAcc (x ∷ xs) a acc with x == a
  ... | true  = acc ++ xs
  ... | false = removeAcc xs a (acc ++ (x ∷ []))
 

private

  module test1 where
  
    _ : remove (1 ∷ 4 ∷ []) 4 ≡ (1 ∷ [])
    _ = refl
    
    _ : remove (1 ∷ 4 ∷ []) 1 ≡ (4 ∷ [])
    _ = refl
  
    _ : remove (1 ∷ 4 ∷ 7 ∷ 9 ∷ []) 1 ≡ (4 ∷ 7 ∷ 9 ∷ [])
    _ = refl
  
    _ : remove (1 ∷ 4 ∷ 7 ∷ 9 ∷ []) 9 ≡ (1 ∷ 4 ∷ 7 ∷ [])
    _ = refl
  
    _ : remove (1 ∷ 4 ∷ 7 ∷ 9 ∷ []) 7 ≡ (1 ∷ 4 ∷ 9 ∷ [])
    _ = refl

-- remove the first matching feature from the label
remove-feature : Label → Feature → Label
remove-feature (mkLabel F uF) f = mkLabel F (remove uF f)  


-- there is an F in l₂ matching the first uF in l₁
check : Label → Label → Bool
check (mkLabel _ []) _ = false
check (mkLabel _ (x ∷ _)) (mkLabel F _) = x ∈ F



-- private
-- n₂ should be maximal
NNMerge : Label → Label → Maybe Label
NNMerge    (mkLabel _ [])      _  = nothing
NNMerge n₁@(mkLabel _ (f ∷ _)) n₂ with check n₁ n₂
... | true  = just (remove-feature n₁ f)
... | false = nothing                          -- merge failed

NMerge : Maybe Label → Maybe Label → Maybe Label
NMerge (just n₁) (just n₂) with n₁ is-maxⁿ | n₂ is-maxⁿ  -- one of n's should be maximal
... | true  | false = NNMerge n₂ n₁
... | false | true  = NNMerge n₁ n₂
... | _     | _ = nothing                      -- merge failed 
NMerge _ _ = nothing

-- adjoins 2 max projections; projects n₂
NAdjoin : Maybe Label → Maybe Label → Maybe Label
NAdjoin (just n₁) (just n₂) with n₁ is-maxⁿ | n₂ is-maxⁿ  -- both should be maximal
... | true  | true  = just n₂
... | _     | _ = nothing                      -- Adjoin failed 
NAdjoin _ _ = nothing

  -- joinz : ∀ m n → Fin (suc m ℕ.+ suc n)
  -- joinz m n = join (suc m) (suc n) (inj₂ zero) 



-- k-th object on the Stage (from the top)
_[_] : ∀ {n : ℕ} → Stage (suc n) → (k : Fin (suc n)) → SO 
infix 30 _[_]

-- Merge labels
LMerge : ∀ {n} → Stage (suc n) → Fin (suc n) → Fin (suc n) → Maybe Label
LMerge s i j = NMerge (lbl (s [ i ])) (lbl (s [ j ]))

-- Adjoin labels
LAdjoin : ∀ {n} → Stage (suc n) → Fin (suc n) → Fin (suc n) → Maybe Label
LAdjoin s i j = NAdjoin (lbl (s [ i ])) (lbl (s [ j ]))




-- the rest of the Stage starting with k
rest : ∀ {n} → Stage (suc n) → (k : Fin (suc n)) → Stage (suc (n ℕ-ℕ k)) --∸ (toℕ k))
rest s zero = s
rest {suc n} (_ & s) (suc k) = rest {n} s k

-- TODO: part-of relation for Stages
-- TODO: dominance, immediate dominance
-- TODO: c-command

private
  k-i : ∀ {n} (k : Fin (suc n)) (i : Fin (suc n)) → Fin (suc (n ℕ-ℕ i ))
  k-i {n} k zero = k
  k-i {suc n} zero (suc i) = zero
  k-i {suc n} (suc k) (suc i) = k-i {n} k i   -- ??

-- a path from the root exists (is dominated by the root)
{-# TERMINATING #-}
path-exists? : ∀ {n} → Stage n → Fin n → Bool

private
  path-check : ∀ {n} → Fin (suc n) → Fin (suc n) → Stage (suc n) → Fin (suc (suc n)) → Bool
  path-check i j s zero = false  --?
  path-check i j s (suc k) with k == i | k == j
  ... | true  | _     = true
  ... | _     | true  = true
  ... | false | false with i 𝔽.<? k | j 𝔽.<? k
  ...                   | no  _ | no  _ = false
  ...                   | yes _ | yes _ = path-exists? (rest s i) (k-i k i) ∨ path-exists? (rest s j) (k-i k j)
  ...                   | yes _ | no  _ = path-exists? (rest s i) (k-i k i)
  ...                   | no  _ | yes _ = path-exists? (rest s j) (k-i k j)
  
path-exists? _ zero = true
path-exists? (Select _ & _) (suc _) = false
path-exists? {suc (suc n)} (Merge  i j & s) (suc k) = path-check i j s (suc k)
path-exists? (Adjoin i j & s) (suc k) = path-check i j s (suc k)

-- c-commandedl : ∀ {n} → Stage n → Fin n → List (Fin n)
-- c-commandedl s i = {!!}



-- -- Move labels; Move j to the place i
-- LMove : ∀ {n} → Stage (suc n) → Fin (suc n) → Fin (suc n) → Maybe Label
-- LMove s i j with path-exists? s i    -- check c-command 
-- ... | false = nothing
-- ... | true  = NMerge (lbl (s [ i ])) (lbl (s [ j ]))


-- is the last Merge internal?
internalMerge? : ∀ {n} → Fin n → Fin n → Stage n → Bool
internalMerge? i j s = path-exists? s i ∨ path-exists? s j



--  _[_] : ∀ {n} → Stage (suc n) → (k : Fin (suc n)) → SO 
(Select x & st)         [ zero ]  = ⟦ x ⊣⟧
(Select {suc n} x & st) [ suc k ] = st [ k ]
(Merge  i j & st)       [ zero ]  = ⟦ LMerge st i j - st [ i ] - st [ j ] ⟧
(Merge  i j & st)       [ suc k ] = st [ k ]
(Adjoin i j & st)       [ zero ]  = ⟦ LAdjoin st i j - st [ i ] - st [ j ] ⟧
(Adjoin i j & st)       [ suc k ] = st [ k ]



-- == Constituents / Parts == --


-- list of constituents (tails, subtrees) -- for SO
ConstituentsSO : SO → List SO
ConstituentsSO s@(⟦ _ ⊣⟧) = s ∷ []
ConstituentsSO s@(⟦ _ - s1 - s2 ⟧) = s ∷ (ConstituentsSO s1 ++ ConstituentsSO s2)

-- part-of relation
_is-a-constituent-of_ : SO → SO → Bool
s is-a-constituent-of st = s ∈ (ConstituentsSO st)


-- list of constituents (tails, subtrees) -- for Stage
Constituents : ∀ {n} → Stage (suc n) → (k : Fin (suc n)) → List SO
Constituents s k = ConstituentsSO (s [ k ])



mapST : ∀{n} → (∀{m} → Node m → Node m) → Stage n → Stage n
mapST f ∅ = ∅
mapST f (x & s) = f x & mapST f s

foldST : ∀ {n} {A : Set} → (∀ {m} → Node m → A → A) → A → Stage n → A
foldST f a ∅ = a
foldST f a (x & s) = f x (foldST f a s)

-- tree : ∀ {n} → Stage n → (k : Fin n) → Stage _ -- (n ℕ-ℕ suc k)
-- tree (x & s) k = {!!}

-- foldSO : ∀ {n} {A : Set} → (∀{m} → Node m → A → A) → A → Stage n → A
-- foldSO f a ∅ = a
-- foldSO f a (n@(Select x) & s) = f n a
-- foldSO {suc n} f a (nd@(Merge i j) & s) = f nd (foldSO f (foldSO f {!!} (rest s j )) (rest s i))
-- foldSO f a (n@(Adjoin i j) & s) = {!!}
