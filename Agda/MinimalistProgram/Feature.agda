-- Minimalist Program in syntax (Chomsky etc.)

module _ where

open import Data.Bool using (true; false; Bool; _∧_)
open import Data.Empty
open import Data.Fin
open import Data.List as List hiding ([_] ; merge; _∷ʳ_)
open import Data.Maybe using (Maybe; just; nothing) 
open import Data.Nat
open import Data.Product 
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open import Agda.Builtin.Reflection
open import Reflection

open import Prelude public


private

  constructors : Definition → List Name
  constructors (data-type pars cs) = cs
  constructors _ = []
  
  vra : {A : Set} → A → Arg A
  vra = arg (arg-info visible (modality relevant quantity-0))
  
  hra : {A : Set} → A → Arg A
  hra = arg (arg-info hidden (modality relevant quantity-0))
  
  -- hetero map
  map2 : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
         → (A → B → C) → List A → List B → List C
  map2 f [] _ = []
  map2 f _ [] = []
  map2 f (x ∷ xs) l = List.map (f x) l ++ map2 f xs l 
  
  map2Maybe : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
              → (A → B → Maybe C) → List A → List B → List C
  map2Maybe f [] _ = []
  map2Maybe f _ [] = []
  map2Maybe f (x ∷ xs) l = List.mapMaybe (f x) l ++ map2Maybe f xs l 

  mk-cls : Name → Name → Clause
  mk-cls q1 q2 with primQNameEquality q1 q2
  ... | true  = clause [] (vra (con q1 []) ∷ vra (con q2 []) ∷ []) (con (quote true)  [])
  ... | false = clause [] (vra (con q1 []) ∷ vra (con q2 []) ∷ []) (con (quote false) [])



module features-adger where

  -- Features. Cf. D.Adger "Core Syntax", p.41.
  
  data FeatureType : Set where
    cCategory : FeatureType
    cPerson cNumber cGender : FeatureType   -- φ -features
    cCase : FeatureType
    cTense : FeatureType
    cWh : FeatureType
    -- cC : FeatureType
    -- Participle : FeatureType
    -- Infinitive : FeatureType
    -- Other : FeatureType
    -- Θ-Role : FeatureType
    -- Wh COMP AGR : FeatureType  -- INFL = AGR + tense
    
  data FeatureVal : FeatureType → Set where
    -- N V Adj P v : FeatureVal Category
    cfirst csecond cthird : FeatureVal cPerson
    csingular cplural cdual : FeatureVal cNumber
    cfem cmasc cneut : FeatureVal cGender
    cNOM cACC cGEN : FeatureVal cCase
    cpast cpresent cfuture : FeatureVal cTense
    cQuestion cDecl : FeatureVal cWh
    -- +part -part : FeatureVal Participle
    -- +inf -inf : FeatureVal Infinitive
    -- part inf : FeatureVal Other
    -- Agent Theme Goal : FeatureVal Θ-Role
    -- +wh -wh : FeatureVal Wh 
  
  data FeatureCore : Set where
    cD cN cV cAdj cP cv cC : FeatureCore
    _⦂_ : (A : FeatureType) → Maybe (FeatureVal A) → FeatureCore


module features-ms where

  -- Митренина, Слюсарь, Романова с.129.

  data FeatureType : Set where
    -- cCategory : FeatureType
    cPerson cNumber cGender : FeatureType   -- φ -features
    cCase : FeatureType
    cTense : FeatureType
    
  data FeatureVal : FeatureType → Set where
    -- N V Adj P v : FeatureVal Category
    c1 c2 c3 : FeatureVal cPerson
    csing cplural cdual : FeatureVal cNumber
    cfem cmasc cneut : FeatureVal cGender
    cNOM cACC cGEN : FeatureVal cCase
    cpast cpres cfut : FeatureVal cTense
    -- +part -part : FeatureVal Participle
    -- +inf -inf : FeatureVal Infinitive
    -- part inf : FeatureVal Other
    -- Agent Theme Goal : FeatureVal Θ-Role
    -- +wh -wh : FeatureVal Wh 
  
  data FeatureCore : Set where
    cD cN cV cAdj cP cv : FeatureCore
    _⦂_ : (A : FeatureType) → Maybe (FeatureVal A) → FeatureCore

-- open features-ms
open features-adger

private

  ddef : Name → TC ⊤
  ddef fname = do
       δ ← getDefinition (quote FeatureType)
       let constrs = constructors δ
       let clauses = map2 mk-cls constrs constrs
       defineFun fname clauses

  _==ᵗ_ : FeatureType → FeatureType → Bool
  unquoteDef _==ᵗ_ = ddef _==ᵗ_ 

  ddef2 : Name → TC ⊤
  ddef2 fname = do
       δ ← getDefinition (quote FeatureVal)
       let constrs = constructors δ
       let clauses = map2 mk-cls constrs constrs
       defineFun fname clauses

  _==ᵛ_ : {A B : FeatureType} → FeatureVal A → FeatureVal B → Bool
  unquoteDef _==ᵛ_ = ddef2 _==ᵛ_ 


instance
  EqVal : {A B : FeatureType} → Eq (FeatureVal A) (FeatureVal B)
  _==_ {{EqVal}} = _==ᵛ_

  EqTyp : Eq (FeatureType) (FeatureType)
  _==_ {{EqTyp}} = _==ᵗ_

private
  mk-cls2 : Name → Name → Maybe Clause
  mk-cls2 (quote _⦂_) q2 = nothing
  mk-cls2 q1 (quote _⦂_) = nothing
  mk-cls2 q1 q2 with primQNameEquality q1 q2
  ... | true  = just (clause [] (vra (con q1 []) ∷ vra (con q2 []) ∷ []) (con (quote true)  []))
  ... | false = just (clause [] (vra (con q1 []) ∷ vra (con q2 []) ∷ []) (con (quote false) []))
  
  mk-clsu : Name → Name → Clause
  mk-clsu q1 q2 = clause (("x" , (vra (def (quote FeatureType) []))) ∷ 
                          ("y" , (vra (def (quote FeatureType) []))) ∷ [])
                         (vra (con (quote _⦂_) (vra (var 1) ∷
                                                vra (con (quote just) (vra (con q1 []) ∷ [])) ∷ [])) ∷ 
                          vra (con (quote _⦂_) (vra (var 0) ∷
                                                vra (con (quote just) (vra (con q2 []) ∷ [])) ∷ [])) ∷ [])
                         (def (quote _==_) ((vra (con q1 [])) ∷ ((vra (con q2 [])) ∷ [])))
  
  ddef3 : Name → TC ⊤
  ddef3 fname = do
       δ ← getDefinition (quote FeatureCore)
       u ← getDefinition (quote FeatureVal)
       let constrs-δ = constructors δ
       let constrs-u = constructors u
       let clauses1 = map2Maybe mk-cls2 constrs-δ constrs-δ
       let clauses2 = clause (("x" , (vra (def (quote FeatureType) []))) ∷ 
                              ("y" , (vra (def (quote FeatureType) []))) ∷ [])
                             (vra (con (quote _⦂_) (vra (var 1) ∷
                                                    vra (con (quote nothing) []) ∷ [])) ∷ 
                              vra (con (quote _⦂_) (vra (var 0) ∷
                                                    vra (con (quote nothing) []) ∷ [])) ∷ [])
                             (def (quote _==_) (vra (var 1 []) ∷ (vra (var 0 []) ∷ []))) ∷ []
       let clauses3 = map2      mk-clsu constrs-u constrs-u
       let clauses4 = clause (("x" , (vra (def (quote FeatureCore) []))) ∷ 
                              ("y" , (vra (def (quote FeatureCore) []))) ∷ [])
                             ((vra (var 1)) ∷ vra (var 0) ∷ [])
                             (con (quote false) []) ∷ []
       let clauses = clauses1 ++ clauses2 ++ clauses3 ++ clauses4
       defineFun fname clauses

  _==ᶠ_ : FeatureCore → FeatureCore → Bool
  unquoteDef _==ᶠ_ = ddef3 _==ᶠ_ 

instance
  EqFeatureCore : Eq FeatureCore FeatureCore
  _==_ {{EqFeatureCore}} = _==ᶠ_


private

  module test1 where
  
    _ : (_ ⦂ just cpast) == (cTense ⦂ just cpast) ≡ true
    _ = refl
    
    _ : (_ ⦂ (just cpast)) == (cTense ⦂ just cpresent) ≡ false
    _ = refl
    
    _ : (cTense ⦂ nothing) == (cTense ⦂ nothing) ≡ true
    _ = refl
    
    _ : (cTense ⦂ just cpast) == (cTense ⦂ nothing) ≡ false
    _ = refl
    
    _ : cN ==ᶠ cAdj ≡ false
    _ = refl
    
    _ : cV ==ᶠ cV ≡ true
    _ = refl
    
    _ : cV == (_ ⦂ just cpast) ≡ false
    _ = refl
    
    _ : cAdj == (cTense ⦂ nothing) ≡ false
    _ = refl


-- List of features

data Strength : Set where
  strong weak : Strength

instance
  EqStrength : Eq Strength Strength
  _==_ {{EqStrength}} strong strong = true
  _==_ {{EqStrength}} weak weak = true
  _==_ {{EqStrength}} _ _ = false


data Opt : Set where
  mandatory optional : Opt

instance
  EqOpt : Eq Opt Opt
  _==_ {{EqOpt}} mandatory mandatory = true
  _==_ {{EqOpt}} optional optional = true
  _==_ {{EqOpt}} _ _ = false

data Feature : Set where
  fea : Opt → Strength → FeatureCore → Feature

instance
  EqFeature : Eq Feature Feature
  _==_ {{EqFeature}} (fea o1 s1 c1) (fea o2 s2 c2) = o1 == o2 ∧ s1 == s2 ∧ c1 == c2

pattern Tᶠ        = fea mandatory weak (cTense ⦂ nothing)
pattern past      = fea mandatory weak (cTense ⦂ just cpast)
pattern past*     = fea mandatory strong (cTense ⦂ just cpast)
pattern present   = fea mandatory weak (cTense ⦂ just cpresent)
pattern present*  = fea mandatory strong (cTense ⦂ just cpresent)
pattern future    = fea mandatory weak (cTense ⦂ just cfuture)
pattern future*   = fea mandatory strong (cTense ⦂ just cfuture)
pattern Cᶠ        = fea mandatory weak cC
pattern V         = fea mandatory weak cV
pattern V*        = fea mandatory strong cV
pattern vᶠ        = fea mandatory weak cv
pattern vᶠ*       = fea mandatory strong cv
pattern N         = fea mandatory weak cN
pattern N*        = fea mandatory strong cN
pattern D         = fea mandatory weak cD
pattern D*        = fea mandatory strong cD
-- pattern n  = fea mandatory weak in
-- pattern n* = fea mandatory strong in
pattern P         = fea mandatory weak cP
pattern P*        = fea mandatory strong cP
pattern ⟨P⟩       = fea optional weak cP
pattern ⟨P*⟩      = fea optional strong cP
pattern Adj       = fea mandatory weak cAdj
pattern Adj*      = fea mandatory strong cAdj
pattern singular  = fea mandatory weak (cNumber ⦂ just csingular)
pattern singular* = fea mandatory strong (cNumber ⦂ just csingular)
pattern plural    = fea mandatory weak (cNumber ⦂ just   cplural)
pattern plural*   = fea mandatory strong (cNumber ⦂ just cplural)
pattern Number:   = fea mandatory weak (cNumber ⦂ nothing)
pattern masc      = fea mandatory weak (cGender ⦂ just cmasc)
pattern fem       = fea mandatory weak (cGender ⦂ just cfem)
pattern first     = fea mandatory weak (cPerson ⦂ just cfirst)
pattern second    = fea mandatory weak (cPerson ⦂ just csecond)
pattern third     = fea mandatory weak (cPerson ⦂ just cthird)
pattern Case:     = fea mandatory weak (cCase ⦂ nothing)
pattern NOM       = fea mandatory weak (cCase ⦂ just cNOM)
pattern ACC       = fea mandatory weak (cCase ⦂ just cACC)
pattern GEN       = fea mandatory weak (cCase ⦂ just cGEN)
pattern Wh:*      = fea mandatory strong (cWh ⦂ nothing)
pattern question  = fea mandatory weak (cWh ⦂ just cQuestion)
pattern decl      = fea mandatory weak (cWh ⦂ just cDecl)
pattern _noval x  = fea mandatory weak (x ⦂ nothing)


FList = List Feature

FListPermutations : FList → List FList
FListPermutations [] = []
FListPermutations l@(x ∷ []) = l ∷ []
FListPermutations (x ∷ xs) = List.foldr (λ fl fls → (add x fl) ++ fls) [] (FListPermutations xs)
  where
  addAcc : Feature → FList → FList → List FList
  addAcc x xacc [] = (xacc List.∷ʳ x) ∷ []
  addAcc x xacc ly@(y ∷ ys) = (addAcc x (xacc List.∷ʳ y) ys) List.∷ʳ (xacc ++ (x ∷ ly)) 

  add : Feature → FList → List FList
  add x xs = addAcc x [] xs


private

  module test2 where
  
    _ : FListPermutations (past* ∷ V ∷ Adj ∷ []) ≡ (Adj ∷ V ∷ past* ∷ []) ∷
                                                   (Adj ∷ past* ∷ V ∷ []) ∷
                                                   (past* ∷ Adj ∷ V ∷ []) ∷
                                                   (V ∷ Adj ∷ past* ∷ []) ∷
                                                   (V ∷ past* ∷ Adj ∷ []) ∷
                                                   (past* ∷ V ∷ Adj ∷ []) ∷ []
    _ = refl                                              


-- without permutations
private
  _==ˡ_ : FList → FList → Bool
  [] ==ˡ [] = true
  (x ∷ xs) ==ˡ (y ∷ ys) = x == y ∧ xs ==ˡ ys
  _ ==ˡ _ = false

-- with permutations
instance
  EqFList : Eq FList FList
  _==_ {{EqFList}} = λ x y → any (λ v → x ==ˡ v) (FListPermutations y)  


private

  module test3 where
  
    _ : (V ∷ past* ∷ []) == (V ∷ past* ∷ []) ≡ true
    _ = refl
    
    _ : (past* ∷ V ∷ []) == (V ∷ past* ∷ []) ≡ true
    _ = refl
    
    _ : (past* ∷ V ∷ Adj ∷ []) == (V ∷ Adj ∷ past* ∷ []) ≡ true
    _ = refl
    
    _ : (past* ∷ Adj ∷ V ∷ N ∷ []) == (N ∷ Adj ∷ V ∷ past* ∷ []) ≡ true
    _ = refl
    
    _ : (Adj ∷ V ∷ N ∷ []) == (N ∷ Adj ∷ V ∷ past* ∷ []) ≡ false
    _ = refl
    
    _ : (V ∷ N ∷ N ∷ []) == (N ∷ V ∷ N ∷ []) ≡ true
    _ = refl


-- FeatureType equality
_==t_ : FeatureCore → FeatureCore → Bool
(A ⦂ _) ==t (B ⦂ _) = A == B
x ==t y = false


-- -- Hierarchy of projections  
-- -- This is actually a feature list (or partial order?)
-- data HoP : Set where
--   ∅   : HoP
--   _⟩_ : {A : FeatureType} → (x : FeatureVal A) → HoP → HoP

-- infixr 5 _⟩_ 

-- vHoP : HoP
-- vHoP = v ⟩ V ⟩ ∅


-- HoP' = FList

-- vHoP' : HoP'
-- vHoP' = v ∷ V ∷ []

-- _∣ : {A : FeatureType} → FeatureVal A → HoP'
-- _∣ x = x ∷ []

-- _⟩'_ : {A : FeatureType} → FeatureVal A → HoP' → HoP'
-- x ⟩' y = x ∷ y

-- infixr 3 _⟩'_
-- infix  5 _∣

-- vHoP'' : HoP'
-- vHoP'' = v ⟩' V ∣

-- sHoP = T ⟩ v ⟩ V ⟩ ∅



record LexItem : Set where
  constructor mkLI
  field
    F  : FList
    uF : FList

record FunCat : Set where
  constructor mkFC
  field
    F  : FList
    uF : FList

infix 4 mkLI mkFC

instance
  EqLI : Eq LexItem LexItem
  _==_ {{EqLI}} (mkLI F1 uF1) (mkLI F2 uF2) = F1 == F2 ∧ uF1 == uF2
  
  EqFC : Eq FunCat FunCat
  _==_ {{EqFC}} (mkFC F1 uF1) (mkFC F2 uF2) = F1 == F2 ∧ uF1 == uF2



--  Lexical array - aka enumeration ------------------

data EnumItem : Set where
  lex : LexItem → EnumItem
  fun : FunCat → EnumItem
  
data Enum : ℕ → Set where                                   -- a la Vec
  _⊣  : EnumItem → Enum (suc zero)
  _∷_ : ∀ {n} → EnumItem → Enum n → Enum (suc n)

instance
  EqNI : Eq EnumItem EnumItem
  _==_ {{EqNI}} (lex x1) (lex x2) = x1 == x2
  _==_ {{EqNI}} (fun x1) (fun x2) = x1 == x2
  _==_ {{EqNI}} _ _ = false

Ehead : ∀ {n} → Enum n → EnumItem
Ehead (x ⊣) = x
Ehead (x ∷ _) = x

Eni : ∀ {n} → Enum n → Fin n → EnumItem
Eni x zero = Ehead x
Eni (li ∷ lis) (suc n) = Eni lis n

Ena : ∀ {n} → Enum (suc n) → (i : Fin (suc n)) → Enum (suc (n ℕ-ℕ i))
Ena x zero = x
Ena (li ∷ (x ⊣)) (suc zero) = x ⊣
Ena (li ∷ (x ∷ lis)) (suc i) = Ena (x ∷ lis) i


-- Etails : ∀ {n} → Enum n → List (ℕ × Enum)
-- Etails [ x ] = suc zero , [ x ] ∷ zero , []
-- Etails l@(_ ∷ la) = l ∷ (Etails la)

Elength : ∀ {n} → Enum n → ℕ
Elength {n} _ = n

_==ˡᵃ_ : ∀ {n₁ n₂} → Enum n₁ → Enum n₂ → Bool
(x ⊣)    ==ˡᵃ (y ⊣)    = x == y
(x ∷ xs) ==ˡᵃ (y ∷ ys) = x == y ∧ xs ==ˡᵃ ys
_ ==ˡᵃ _ = false

-- without permutations -- not necessary
instance
  EqEnum : ∀ {n₁ n₂} → Eq (Enum n₁) (Enum n₂)
  _==_ {{EqEnum}} = _==ˡᵃ_


