-- Syntax Object as Binary Tree

-- TODO: dominance, immediate dominance
-- TODO: все понятия X' теории


-- open import Data.String.Base using (_++_)
-- open import Debug.Trace

module BTree.SyntaxObject where

open import Data.Bool
open import Data.Fin hiding (_-_; _>_) 
open import Data.List as 𝕃 hiding ([_]; foldl; foldr)
open import Data.Maybe hiding (map)
open import Data.Nat hiding (_>_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Feature public


--=== Lexical items, lexemes ===--

-- нужно ли различать lex и fun?

record LexItem : Set where
  constructor mkLI
  field
    Phon : PHONList
    Sem  : SEMList
    F    : SYNList
    uF   : SYNList

infix 4 mkLI 

instance
  EqLI : Eq LexItem LexItem
  _==_ {{EqLI}} (mkLI PL1 SL1 F1 uF1) (mkLI PL2 SL2 F2 uF2) =
       _==_ {{EqLPHON}} PL1 PL2 ∧ _==_ {{EqLSEM}} SL1 SL2 ∧ F1 == F2 ∧ uF1 == uF2
  


--===  Lexical array (numeration? No!) ===--


data LexArr : Set where                                   
  [_] : LexItem → LexArr
  _∷_ : LexItem → LexArr → LexArr 


LA→List : LexArr → List LexItem
LA→List [ x ] = x ∷ []
LA→List (x ∷ xs) = x ∷ (LA→List xs)

LAhead : LexArr → LexItem
LAhead [ x ] = x
LAhead (x ∷ _) = x

LAtail : LexArr → List LexItem
LAtail [ x ] = []
LAtail (_ ∷ xs) = LA→List xs

LAlength : LexArr → ℕ
LAlength [ _ ] = 1
LAlength (_ ∷ xs) = suc (LAlength xs)

LAith : (la : LexArr) → Fin (LAlength la) → LexItem
LAith [ x ] zero = x
LAith (li ∷ _) zero = li
LAith (_ ∷ lis) (suc n) = LAith lis n


_==ˡᵃ_ : LexArr → LexArr → Bool
[ x ]    ==ˡᵃ [ y ]    = x == y
(x ∷ xs) ==ˡᵃ (y ∷ ys) = x == y ∧ xs ==ˡᵃ ys
_ ==ˡᵃ _ = false


-- without permutations -- permutations aren't necessary
instance
  EqLA : Eq LexArr LexArr 
  _==_ {{EqLA}} = _==ˡᵃ_




--=== Label ===--

record Label : Set where
  constructor mkLabel   
  field
    Phon : PHONList
    Sem  : SEMList
    F    : SYNList
    uF   : SYNList

pattern _∙_∙_∙_ p s x y = just (mkLabel p s x y)

infix 4 mkLabel _∙_∙_∙_

instance
  EqLabel : Eq Label Label
  _==_ {{EqLabel}} (mkLabel P₁ S₁ F₁ uF₁) (mkLabel P₂ S₂ F₂ uF₂) = 
       _==_ {{EqLPHON}} P₁ P₂ ∧ _==_ {{EqLSEM}} S₁ S₂ ∧ F₁ == F₂ ∧ uF₁ == uF₂

LI→Label : LexItem → Label
LI→Label (mkLI p s F uF) = mkLabel p s F uF

Label→LI : Label → LexItem
Label→LI (mkLabel p s F uF) = mkLI p s F uF

-- the label of the head
LA→Label : LexArr → Label
LA→Label x = LI→Label (LAhead x)



--=== Syntax Tree and Syntax Object ===--

-- Syntax object
data SO : Set where
  ⟦_⟧    : LexArr → SO                      -- selected (from LexArr)
  ⟦_-_-_⟧ : Maybe Label → SO → SO → SO       -- merge

-- infix 7 ⟦_⟧
infixr 6 ⟦_-_-_⟧

instance
  EqSO : Eq SO SO
  _==_ ⦃ EqSO ⦄ ⟦ x1 ⟧ ⟦ x2 ⟧ = x1 == x2 
  _==_ ⦃ EqSO ⦄ ⟦ x1 - s11 - s12 ⟧ ⟦ x2 - s21 - s22 ⟧ =
       x1 == x2 ∧ ((s11 == s21 ∧ s12 == s22) ∨ (s11 == s22 ∧ s12 == s21)) -- no order 
  _==_ ⦃ EqSO ⦄ _ _ = false



-- the label of SO
lbl : SO → Maybe Label
lbl ⟦ x ⟧ = just (LA→Label x)
lbl ⟦ x - _ - _ ⟧ = x

-- decomposing Merge  (???)
unMergel : SO → SO
unMergel ⟦ x ⟧ = ⟦ x ⟧
unMergel ⟦ _ - s - _ ⟧ = s

unMerger : SO → SO
unMerger ⟦ x ⟧ = ⟦ x ⟧
unMerger ⟦ _ - _ - s ⟧ = s


-- maximal projection for Labels
_is-maxˡ : Label → Bool
_is-maxˡ (mkLabel _ _ _ []) = true
_is-maxˡ _ = false

-- maximal projection
_is-max : SO → Bool
_is-max s = is-maxˡ-Maybe (lbl s)
  where
  is-maxˡ-Maybe : Maybe Label → Bool
  is-maxˡ-Maybe (_ ∙ _ ∙ _ ∙ []) = true
  is-maxˡ-Maybe _ = false

-- minimal projection
_is-min : SO → Bool
⟦ _ ⟧ is-min = true
_ is-min = false



-- ================================================================

private

  -- unchecked SYN feature exists
  {-# TERMINATING #-}
  feature-exists? : SYN → Label → Bool
  feature-exists? _ (mkLabel _ _ _ []) = false
  feature-exists? f (mkLabel p s F (uf ∷ ufs)) with f == uf
  ... | true  = true
  ... | false = feature-exists? f (mkLabel p s F ufs)
  
  -- remove the first matching feature from the label
  remove-feature : SYN → Label → Label
  remove-feature f (mkLabel p s F uF) = mkLabel p s F (remove-first uF f)  

  -- there is an F in l₂ matching the first uF in l₁
  check : Label → Label → Bool
  check (mkLabel _ _ _ []) _ = false
  check (mkLabel _ _ _ (x ∷ _)) (mkLabel _ _ F _) = x ∈ F

  -- n₂ should be maximal
  LMerge' : Label → Label → Maybe Label
  LMerge'    (mkLabel _ _ _ [])      _  = nothing
  LMerge' n₁@(mkLabel _ _ _ (f ∷ _)) n₂ with check n₁ n₂
  ... | true  = just (remove-feature f n₁)
  ... | false = nothing                          -- merge failed

LMerge : Maybe Label → Maybe Label → Maybe Label
LMerge (just n₁) (just n₂) with n₁ is-maxˡ | n₂ is-maxˡ  
... | true  | false = LMerge' n₂ n₁
... | false | true  = LMerge' n₁ n₂
... | true  | true  = just n₂             -- Adjoin actually, n₂ projected
... | _     | _ = nothing                 -- merge failed 
LMerge _ _ = nothing



-- Syntax tree -- derivation steps without labels

data DTree : Set where
  Select : LexArr → DTree
  Merge  : DTree → DTree → DTree

DTree→SO : DTree → SO
DTree→SO (Select x)     = ⟦ x ⟧
DTree→SO (Merge s₁ s₂)  = ⟦ LMerge  (lbl so₁) (lbl so₂) - so₁ - so₂ ⟧
  where
  so₁ = DTree→SO s₁
  so₂ = DTree→SO s₂

SO→DTree : SO → DTree
SO→DTree ⟦ x ⟧ = Select x
SO→DTree ⟦ _ - s1 - s2 ⟧ = Merge (SO→DTree s1) (SO→DTree s2) 


-- ???  -- very strange definition
-- map : (SO → SO) → SO → SO
-- map f s@(⟦ _ ⟧) = f s
-- map f ⟦ _ - s1 - s2 ⟧ = ⟦ LMerge (lbl s1') (lbl s2') - s1' - s2' ⟧
--   where
--   s1' = map f s1
--   s2' = map f s2

foldl : {A : Set} → (SO → SO → A → A) → A → SO → A
foldl _ a ⟦ x ⟧ = a
foldl f a ⟦ _ - s1 - s2 ⟧ = foldl f (foldl f (f s1 s2 a) s1) s2

foldr : {A : Set} → (SO → A → A → A) → (SO → A) → SO → A
foldr _ g s@(⟦ _ ⟧) = g s
foldr f g s@(⟦ _ - s1 - s2 ⟧) = f s (foldr f g s1) (foldr f g s2)

foldrLbl : {A : Set} → (Maybe Label → A → A → A) → (Label → A) → SO → A
foldrLbl _ g ⟦ x ⟧ = g (LA→Label x)
foldrLbl f g ⟦ x - s1 - s2 ⟧ = f x (foldrLbl f g s1) (foldrLbl f g s2) 


-- number of nodes
nodesNum : SO → ℕ
nodesNum so = foldl f 1 so
  where
  f : SO → SO → ℕ → ℕ
  f _ _ n = (suc (suc n))

-- number of edges
edgesNum : SO → ℕ
edgesNum so = foldr f g so
  where
  f : SO → ℕ → ℕ → ℕ
  f _ n m = (suc n) Data.Nat.+ (suc m)

  g : SO → ℕ
  g _ = zero

    

--== Constituents / Parts ==--


-- list of constituents (tails, subtrees) -- for SO
Constituents : SO → List SO
Constituents so = foldl f (so ∷ []) so
  where
  f : SO → SO → List SO → List SO
  f so1 so2 sos = sos ∷ʳ so1 ∷ʳ so2

-- another definition (equivalent actually)
Constituents' : SO → List SO
Constituents' s@(⟦ _ ⟧) = s ∷ []
Constituents' s@(⟦ _ - s1 - s2 ⟧) = s ∷ (Constituents' s1 ++ Constituents' s2)



-- part-of relation
_containsᵇ_ : SO → SO → Bool
so containsᵇ s = s ∈ (Constituents so)


infixl 5 _cl _cr

data _contains_ : SO → SO → Set where
  c0  : {s : SO} → s contains s          -- root is a constituent
  _cl : {s s1 s2 : SO} {l : Maybe Label} → 
        (s contains ⟦ l - s1 - s2 ⟧) → s contains s1 
  _cr : {s s1 s2 : SO} {l : Maybe Label} → 
        (s contains ⟦ l - s1 - s2 ⟧) → s contains s2  

-- path from ... to ...  -- equivalent to 'contains'
path_to_ : SO → SO → Set 
path s0 to s = s0 contains s

-- TODO: Are 'contains' and 'containsᵇ' equivalent?

-- t1 : (s s0 : SO) → s0 contains s → s0 containsᵇ s ≡ true
-- t1 s .s c0 = {!refl!}
-- t1 s s0 (cl p) = {!!}
-- t1 s s0 (cr p) = {!!}

-- t2 : (s s0 : SO) → s0 containsᵇ s ≡ true → s0 contains s
-- t2 ⟦ x ⟧ s p = {!c0!}
-- t2 ⟦ x - s1 - s2 ⟧ s p = {!!}


-- type of positions for s0 = type of paths from s0
data Position (s0 : SO) : Set where
  pos : {s : SO} → s0 contains s → Position s0


-- position of s in s0
Path→List : {s0 s : SO} → path s0 to s → List SO
Path→List {s0} c0 = s0 ∷ []
Path→List {_} {s} (p cl) = (Path→List p) ∷ʳ s   
Path→List {_} {s} (p cr) = (Path→List p) ∷ʳ s   

-- path in the form of List
Pos→List : {s : SO} → Position s → List SO
Pos→List (pos p) = Path→List p

-- the last SO in position
Pos→SO : {s0 : SO} → Position s0 → SO
Pos→SO (pos {s} p) = s


internalMerge? : SO → Bool
internalMerge? ⟦ _ ⟧ = false           -- not a Merge
internalMerge? ⟦ _ - s₁ - s₂ ⟧ = (s₁ containsᵇ s₂) ∨ (s₂ containsᵇ s₁)



--== c-command ==--

-- path concatenation
-- looks like a theorem
_>_ : {s0 s1 s2 : SO} → path s0 to s1 → path s1 to s2 → path s0 to s2
p01 > c0 = p01
p01 > (p12' cl) = (p01 > p12') cl
p01 > (p12' cr) = (p01 > p12') cr

-- prepending path to position
prependPath : {s0 s1 : SO} → path s0 to s1 → Position s1 → Position s0
prependPath c (pos x) = pos (c > x)

-- all paths starting from s0
positions : (s0 : SO) → List (Position s0)
positions ⟦ _ ⟧ = pos c0 ∷ []
positions ⟦ _ - s1 - s2 ⟧ = pos c0 ∷ map (prependPath (c0 cl)) (positions s1) ++
                                     map (prependPath (c0 cr)) (positions s2) 

-- positions/paths as List
positionsSO : SO → List (List SO)
positionsSO so = map Pos→List (positions so)

-- alternative definition
positionsSO' : SO → List (List SO)
positionsSO' s = foldr f g s
  where
  append : SO → List (List SO) → List (List SO)
  append s [] = []
  append s (ss ∷ sss) = (s ∷ ss) ∷ append s sss

  f : SO → List (List SO) → List (List SO) → List (List SO)
  f so sos1 sos2 = (so ∷ []) ∷ ((append so sos1) ++ (append so sos2))
  
  g : SO → List (List SO)
  g s = (s ∷ []) ∷ []


sister : {s0 : SO} → Position s0 → Maybe (Position s0)
sister (pos c0) = nothing
sister (pos (x cl)) = just (pos (x cr))
sister (pos (x cr)) = just (pos (x cl))

sisterL : {s0 : SO} → Position s0 → Maybe SO
sisterL (pos c0) = nothing
sisterL (pos (x cl)) = just (Pos→SO (pos (x cr)))
sisterL (pos (x cr)) = just (Pos→SO (pos (x cl)))


-- the list of c-commanded positions
c-commanded : {s0 : SO} → Position s0 → List (Position s0)
c-commanded (pos c0) = []
c-commanded (pos (x cl)) = map (prependPath (x cr)) (positions (Pos→SO (pos (x cr))))
c-commanded (pos (x cr)) = map (prependPath (x cl)) (positions (Pos→SO (pos (x cl))))

c-commandedL : {s0 : SO} → Position s0 → List (List SO)
c-commandedL p = map Pos→List (c-commanded p)


-- chain = List of positions
chainL : SO → SO → List (List SO)
chainL s s0 = flt (lasteq s) [] (positionsSO s0)
  where
  lasteq : SO → List SO → Bool
  lasteq s [] = false
  lasteq s (x ∷ []) = s == x
  lasteq s (x ∷ xs) = lasteq s xs
  
  flt : {A : Set} → (A → Bool) → List A → List A → List A
  flt f acc [] = acc
  flt f acc (x ∷ xs) with f x
  ... | true  = flt f (acc ∷ʳ x) xs
  ... | false = flt f acc xs


