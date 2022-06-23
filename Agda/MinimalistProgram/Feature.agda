-- Minimalist Program in syntax (Chomsky etc.)

module _ where

open import Data.Bool using (true; false; Bool; _∧_)
open import Data.Empty
open import Data.Fin
open import Data.List as 𝕃 hiding ([_] ; merge; _∷ʳ_)
open import Data.Maybe using (Maybe; just; nothing) 
open import Data.Nat
open import Data.Product 
open import Data.String hiding (_++_; _==_) 
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open import Agda.Builtin.Reflection
open import Reflection

open import Prelude public
open import ReflectionFunctions public


-- for simplicity PHON and SEM are Strings
PHON = String
SEM = String


-- SYN features

module features-adger where

  -- Features. Cf. D.Adger "Core Syntax", p.41.
  
  data SYNType : Set where
    cCategory : SYNType
    cPerson cNumber cGender : SYNType   -- φ -features
    cCase : SYNType
    cTense : SYNType
    cWh : SYNType
    -- cC : SYNType
    -- Participle : SYNType
    -- Infinitive : SYNType
    -- Other : SYNType
    -- Θ-Role : SYNType
    -- Wh COMP AGR : SYNType  -- INFL = AGR + tense
    
  data SYNVal : SYNType → Set where
    -- N V A P v : SYNVal Category
    cfirst csecond cthird : SYNVal cPerson
    csingular cplural cdual : SYNVal cNumber
    cfem cmasc cneut : SYNVal cGender
    cNOM cACC cGEN : SYNVal cCase
    cpast cpresent cfuture : SYNVal cTense
    cQuestion cDecl : SYNVal cWh
    -- +part -part : SYNVal Participle
    -- +inf -inf : SYNVal Infinitive
    -- part inf : SYNVal Other
    -- Agent Theme Goal : SYNVal Θ-Role
    -- +wh -wh : SYNVal Wh
    none : {A : SYNType} → SYNVal A
    yes  : {A : SYNType} → SYNVal A
    no   : {A : SYNType} → SYNVal A
  
  data SYNCore : Set where
    cD cN cV cA cP cv cC : SYNCore
    _⦂_ : (A : SYNType) → SYNVal A → SYNCore


module features-ms where

  -- Митренина, Слюсарь, Романова с.129.

  data SYNType : Set where
    -- cCategory : SYNType
    cPerson cNumber cGender : SYNType   -- φ -features
    cCase : SYNType
    cTense : SYNType
    
  data SYNVal : SYNType → Set where
    -- N V A P v : SYNVal Category
    c1 c2 c3 : SYNVal cPerson
    csing cplural cdual : SYNVal cNumber
    cfem cmasc cneut : SYNVal cGender
    cNOM cACC cGEN : SYNVal cCase
    cpast cpres cfut : SYNVal cTense
    -- +part -part : SYNVal Participle
    -- +inf -inf : SYNVal Infinitive
    -- part inf : SYNVal Other
    -- Agent Theme Goal : SYNVal Θ-Role
    -- +wh -wh : SYNVal Wh 
    -- none : {A : SYNType} → SYNVal A
  
  data SYNCore : Set where
    cD cN cV cA cP cv : SYNCore
    _⦂_ : (A : SYNType) → SYNVal A → SYNCore

-- open features-ms
open features-adger


private

  deftyp : Name → TC ⊤
  deftyp fname = do
       δ ← getDefinition (quote SYNType)
       let constrs = constructors δ
       let clauses = map2 mk-cls constrs constrs
       defineFun fname clauses

  _==ᵗ_ : SYNType → SYNType → Bool
  unquoteDef _==ᵗ_ = deftyp _==ᵗ_ 

  defval : Name → TC ⊤
  defval fname = do
       δ ← getDefinition (quote SYNVal)
       let constrs = constructors δ
       let clauses = map2 mk-cls constrs constrs
       defineFun fname clauses

  _==ᵛ_ : {A B : SYNType} → SYNVal A → SYNVal B → Bool
  unquoteDef _==ᵛ_ = defval _==ᵛ_ 


instance
  EqVal : {A B : SYNType} → Eq (SYNVal A) (SYNVal B)
  _==_ {{EqVal}} = _==ᵛ_

  EqTyp : Eq (SYNType) (SYNType)
  _==_ {{EqTyp}} = _==ᵗ_

private

  mk-cls2 : Name → Name → Maybe Clause
  mk-cls2 (quote _⦂_) q2 = nothing
  mk-cls2 q1 (quote _⦂_) = nothing
  mk-cls2 q1 q2 with primQNameEquality q1 q2
  ... | true  = just (clause [] (vra (con q1 []) ∷ vra (con q2 []) ∷ [])
                             (con (quote true)  []))
  ... | false = just (clause [] (vra (con q1 []) ∷ vra (con q2 []) ∷ [])
                             (con (quote false) []))
  
  ddef3 : Name → TC ⊤
  ddef3 fname = do
       δ ← getDefinition (quote SYNCore)
       let constrs-δ = constructors δ
       let clauses1 = map2Maybe mk-cls2 constrs-δ constrs-δ   -- skip _⦂_
       let clause2  = clause (("x1" , (vra (def (quote SYNType) []))) ∷ 
                              ("x2" , (vra (def (quote SYNType) []))) ∷ 
                              ("y1" , (vra (def (quote SYNVal) (vra (var 1 []) ∷ [])))) ∷ 
                              ("y2" , (vra (def (quote SYNVal) (vra (var 1 []) ∷ [])))) ∷ [])
                             (vra (con (quote _⦂_) (vra (var 2) ∷ vra (var 0) ∷ [])) ∷ 
                              vra (con (quote _⦂_) (vra (var 3) ∷ vra (var 1) ∷ [])) ∷ [])
                             (def (quote _∧_) (vra (def (quote _==_) (vra (var 3 []) ∷
                                                                     (vra (var 2 []) ∷ []))) ∷
                                               vra (def (quote _==_) (vra (var 1 []) ∷
                                                                     (vra (var 0 []) ∷ []))) ∷
                                               [])) ∷ []
       let clause3  = clause (("x" , (vra (def (quote SYNCore) []))) ∷         -- "false" clause
                              ("y" , (vra (def (quote SYNCore) []))) ∷ [])
                             ((vra (var 1)) ∷ vra (var 0) ∷ [])
                             (con (quote false) []) ∷ []
       let clauses = clauses1 ++ clause2 ++ clause3
       defineFun fname clauses

  _==ᶠ_ : SYNCore → SYNCore → Bool
  unquoteDef _==ᶠ_ = ddef3 _==ᶠ_
  

instance
  EqSYNCore : Eq SYNCore SYNCore
  _==_ {{EqSYNCore}} = _==ᶠ_


private

  module test1 where
  
    _ : (_ ⦂ cpast) == (cTense ⦂ cpast) ≡ true
    _ = refl
    
    _ : (_ ⦂ (cpast)) == (cTense ⦂ cpresent) ≡ false
    _ = refl
    
    _ : (cTense ⦂ none) == (cTense ⦂ none) ≡ true
    _ = refl
    
    _ : (cTense ⦂ cpast) == (cTense ⦂ none) ≡ false
    _ = refl
    
    _ : cN ==ᶠ cA ≡ false
    _ = refl
    
    _ : cV ==ᶠ cV ≡ true
    _ = refl
    
    _ : cV == (_ ⦂ cpast) ≡ false
    _ = refl
    
    _ : cA == (cTense ⦂ none) ≡ false
    _ = refl



-- Second order properties of features?

data Strength : Set where
  strong weak : Strength    -- EPP?

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

data SYN : Set where
  fea : Opt → Strength → SYNCore → SYN

instance
  EqSYN : Eq SYN SYN
  _==_ {{EqSYN}} (fea o1 s1 c1) (fea o2 s2 c2) = o1 == o2 ∧ s1 == s2 ∧ c1 == c2

pattern Tᶠ        = fea mandatory weak (cTense ⦂ none)
pattern past      = fea mandatory weak (cTense ⦂ cpast)
pattern past*     = fea mandatory strong (cTense ⦂ cpast)
pattern present   = fea mandatory weak (cTense ⦂ cpresent)
pattern present*  = fea mandatory strong (cTense ⦂ cpresent)
pattern future    = fea mandatory weak (cTense ⦂ cfuture)
pattern future*   = fea mandatory strong (cTense ⦂ cfuture)
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
pattern A       = fea mandatory weak cA
pattern A*      = fea mandatory strong cA
pattern singular  = fea mandatory weak (cNumber ⦂ csingular)
pattern singular* = fea mandatory strong (cNumber ⦂ csingular)
pattern plural    = fea mandatory weak (cNumber ⦂   cplural)
pattern plural*   = fea mandatory strong (cNumber ⦂ cplural)
pattern Number:   = fea mandatory weak (cNumber ⦂ none)
pattern masc      = fea mandatory weak (cGender ⦂ cmasc)
pattern fem       = fea mandatory weak (cGender ⦂ cfem)
pattern first     = fea mandatory weak (cPerson ⦂ cfirst)
pattern second    = fea mandatory weak (cPerson ⦂ csecond)
pattern third     = fea mandatory weak (cPerson ⦂ cthird)
pattern Case:     = fea mandatory weak (cCase ⦂ none)
pattern NOM       = fea mandatory weak (cCase ⦂ cNOM)
pattern ACC       = fea mandatory weak (cCase ⦂ cACC)
pattern GEN       = fea mandatory weak (cCase ⦂ cGEN)
pattern Wh:*      = fea mandatory strong (cWh ⦂ none)
pattern question  = fea mandatory weak (cWh ⦂ cQuestion)
pattern decl      = fea mandatory weak (cWh ⦂ cDecl)
pattern _noval x  = fea mandatory weak (x ⦂ none)


-- Match - SYNType equality
_==t_ : SYNCore → SYNCore → Bool
(X ⦂ _) ==t (Y ⦂ _) = X == Y
x ==t y = false


-- Feature lists ------------------

PHONList = List PHON
SEMList  = List SEM
SYNList  = List SYN


-- without permutations
private
  _==ˡ_ : {A : Set} → {{Eq A A}} → (List A) → (List A) → Bool
  [] ==ˡ [] = true
  (x ∷ xs) ==ˡ (y ∷ ys) = x == y ∧ xs ==ˡ ys
  _ ==ˡ _ = false

  _∈ˡ_ : {A : Set} → {{Eq A A}} → (List A) → List (List A) → Bool
  x ∈ˡ [] = false
  x ∈ˡ (v ∷ vs) with x ==ˡ v
  ... | true  = true
  ... | false = x ∈ˡ vs


-- with permutations

private

  module test2 where

    _ : ListPermutations (N ∷ []) ≡ (N ∷ []) ∷ []
    _ = refl
    
    _ : ListPermutations (past* ∷ V ∷ A ∷ []) ≡ (A ∷ V ∷ past* ∷ []) ∷
                                                 (A ∷ past* ∷ V ∷ []) ∷
                                                 (past* ∷ A ∷ V ∷ []) ∷
                                                 (V ∷ A ∷ past* ∷ []) ∷
                                                 (V ∷ past* ∷ A ∷ []) ∷
                                                 (past* ∷ V ∷ A ∷ []) ∷ []
    _ = refl                                              


instance
  EqList : {A : Set} → {{Eq A A}} → Eq (List A) (List A)
  _==_ {{EqList}} x y = x ∈ˡ (ListPermutations y)  

  -- EqSYNList : Eq SYNList SYNList
  -- _==_ {{EqSYNList}} x y = x ∈ˡ (SYNListPermutations y)  
  -- -- _==_ {{EqSYNList}} = λ x y → any (λ v → x ==ˡ v) (SYNListPermutations y)  

  -- EqPHON : Eq PHON PHON
  -- _==_ {{EqPHON}} (phon x1) (phon x2) = x1 == x2
  EqPHON = EqString
  
  EqLPHON : Eq (List PHON) (List PHON)
  EqLPHON = EqList {PHON}

  -- EqSEM : Eq SEM SEM
  -- _==_ {{EqSEM}} (sem x1) (sem x2) = x1 == x2
  EqSEM = EqString

  EqLSEM : Eq (List SEM) (List SEM)
  EqLSEM = EqList {SEM}

private

  module test3 where
  
    _ : (V ∷ past* ∷ []) == (V ∷ past* ∷ []) ≡ true
    _ = refl
    
    _ : (past* ∷ V ∷ []) == (V ∷ past* ∷ []) ≡ true
    _ = refl
    
    _ : (past* ∷ V ∷ A ∷ []) == (V ∷ A ∷ past* ∷ []) ≡ true
    _ = refl
    
    _ : (past* ∷ A ∷ V ∷ N ∷ []) == (N ∷ A ∷ V ∷ past* ∷ []) ≡ true
    _ = refl
    
    _ : (A ∷ V ∷ N ∷ []) == (N ∷ A ∷ V ∷ past* ∷ []) ≡ false
    _ = refl
    
    _ : (V ∷ N ∷ N ∷ []) == (N ∷ V ∷ N ∷ []) ≡ true
    _ = refl



-- -- Hierarchy of projections  
-- -- This is actually a feature list (or partial order?)
-- data HoP : Set where
--   ∅   : HoP
--   _⟩_ : {A : SYNType} → (x : SYNVal A) → HoP → HoP

-- infixr 5 _⟩_ 

-- vHoP : HoP
-- vHoP = v ⟩ V ⟩ ∅


-- HoP' = SYNList

-- vHoP' : HoP'
-- vHoP' = v ∷ V ∷ []

-- _∣ : {A : SYNType} → SYNVal A → HoP'
-- _∣ x = x ∷ []

-- _⟩'_ : {A : SYNType} → SYNVal A → HoP' → HoP'
-- x ⟩' y = x ∷ y

-- infixr 3 _⟩'_
-- infix  5 _∣

-- vHoP'' : HoP'
-- vHoP'' = v ⟩' V ∣

-- sHoP = T ⟩ v ⟩ V ⟩ ∅
