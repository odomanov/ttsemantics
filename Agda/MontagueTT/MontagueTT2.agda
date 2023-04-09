-- Montague semantics in terms of TT.
-- Допускаем синтаксически правильные, но семантически неправильные выражения.

-- Здесь синтаксические категории не зависят от CN.  Они сначала
-- переводятся в категории, зависящие от CN -- sCN, sNP и пр., а затем для
-- них формулируется семантика прежним образом.

module _ where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; _∷_; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_)
open import Data.Unit using (⊤; tt)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym; cong₂)
open import Relation.Nullary renaming (no to not)  --using (Dec; yes; ¬_) 
open import Relation.Nullary.Decidable.Core using (map′)

open import ReflectionEq


-- The structure to hold names
-- ===========================

record LexStructure : Set₁ where
  field
    nameCN namePN nameVI nameVT nameAdj : Set  -- names for syntactic categories
    eqCN   : (x y : nameCN)  → Dec (x ≡ y)    -- разрешимые равенства для имён
    eqPN   : (x y : namePN)  → Dec (x ≡ y)
    eqVI   : (x y : nameVI)  → Dec (x ≡ y)
    eqVT   : (x y : nameVT)  → Dec (x ≡ y)
    eqAdj  : (x y : nameAdj) → Dec (x ≡ y)


-- Синтаксические категории.
-- ========================

module Syntax (lex : LexStructure) where

  open LexStructure lex
              
  mutual
  
    data CN : Set where
      cn-n  : nameCN → CN
      cn-ap : AP → CN
      rcn   : CN → VP → CN    -- CN that VP
      
    data VI : Set where
      vi-n : nameVI → VI 
  
    data VT : Set where
      vt-n : nameVT → VT
      
    data PN : Set where
      pn-n : namePN → PN   
    
    data DET : Set where
      a/an every no the ∅ : DET
  
    data Adj : Set where
      adj-n : nameAdj → Adj
      
    data VP : Set where
      vp-vi : VI → VP 
      vp-vt : VT → NP → VP 
    
    data NP : Set where
      np-pn  : PN → NP 
      np-det : DET → CN → NP 
    
    data AP : Set where
      ap-a : Adj → AP
      
    data S : Set where
      s-nv  : NP → VP → S
      s-nvn : NP → VT → NP → S


  -- примеры

  private
  
    -- every man runs
    _ : S
    _ = s-nv (np-det every man) (vp-vi runs)
      where postulate
              man : CN
              runs : VI

    -- green ideas sleep
    _ : S
    _ = s-nv (np-det ∅ ideas) (vp-vi sleep)
      where postulate
              green  : Adj
              ideas   : CN
              sleep : VI




-- Семантика
-- =========

-- В модели валюации имён содержат их зависимость от CN

record Model (lex : LexStructure) : Set₁ where
  open LexStructure lex
  field
    valCN  : nameCN  → Set
    valPN  : namePN  → Σ[ cn ∈ nameCN ] (valCN cn) 
    valVI  : nameVI  → Σ[ cn ∈ nameCN ] (valCN cn → Set)
    valVT  : nameVT  → Σ[ cn1 ∈ nameCN ] Σ[ cn2 ∈ nameCN ] (valCN cn1 → valCN cn2 → Set)
    valAdj : nameAdj → Σ[ cn ∈ nameCN ] (valCN cn → Set)


module Semantics (lex : LexStructure) (m : Model lex) where

  open LexStructure lex
  open Syntax lex public
  open Model m

  -- Первый шаг интерпретации: определяем категории, зависящие от CN.
  
  mutual
  
    data sCN : Set where
      cn-n  : nameCN → sCN
      cn-ap : {cn : sCN} → sAP cn → sCN
      rcn   : (cn : sCN) → sVP cn → sCN    -- CN that VP
      
    data sVI : sCN → Set where
      vi-n : (n : nameVI) → sVI (cn-n (proj₁ (valVI n)))
  
    -- порядок аргументов в VT прямой!  VT A B => A → B → Set
    data sVT : sCN → sCN → Set where
      vt-n : (n : nameVT) → sVT (cn-n (proj₁ (valVT n))) (cn-n (proj₁ (proj₂ (valVT n))))
      
    data sPN : sCN → Set where
      pn-n : (n : namePN) → sPN (cn-n (proj₁ (valPN n)))
    
    data sDET : Set where
      a/an every no the ∅ : sDET
  
    data sAdj : sCN → Set where
      adj-n : (n : nameAdj) → sAdj (cn-n (proj₁ (valAdj n)))
      
    data sVP (cn : sCN) : Set where
      vp-vi : sVI cn → sVP cn
      vp-vt : ∀ {cn1} → sVT cn cn1 → sNP cn1 → sVP cn
    
    data sNP : (cn : sCN) → Set where
      np-pn  : ∀ {cn} → sPN cn → sNP cn
      np-det : sDET → (cn : sCN) → sNP cn
    
    data sAP (cn : sCN) : Set where
      ap-a : sAdj cn → sAP cn
      
    data sS : Set where
      s-nv  : ∀ {cn} → sNP cn → sVP cn → sS
      s-nvn : ∀ {cn1 cn2} → sNP cn1 → sVT cn1 cn2 → sNP cn2 → sS


  -- Определяем разрешимое равенство для sCN, sPN,...
  
  -- Для зависимых от sCN категорий вида sCN → A определяем равенство для
  -- Dec ((cx , x) ≡ (cy , y)), т.е.  они равны, если равны как (cx cy : sCN),
  -- так и они сами, т.е. (x : A cx), (y : A cy).
  
  mutual

    _≟CN_ : (x y : sCN) → Dec (x ≡ y)
    cn-n x ≟CN cn-n y = map′ (cong cn-n) f (eqCN x y)
      where
      f : {x y : nameCN} → (sCN.cn-n x ≡ cn-n y) → x ≡ y
      f refl = refl
    cn-ap {cx} x ≟CN cn-ap {cy} y = map′ f g (x ≟AP y)
      where
      f : (cx , x) ≡ (cy , y) → cn-ap x ≡ cn-ap y
      f refl = refl
      g : cn-ap x ≡ cn-ap y → (cx , x) ≡ (cy , y)
      g refl = refl
    rcn cx vx ≟CN rcn cy vy = map′ f g (vx ≟VP vy)
      where
      f : (cx , vx) ≡ (cy , vy) → rcn cx vx ≡ rcn cy vy
      f refl = refl
      g : rcn cx vx ≡ rcn cy vy → (cx , vx) ≡ (cy , vy)
      g refl = refl
    cn-n _ ≟CN cn-ap _  = not (λ ())
    cn-n _ ≟CN rcn _ _  = not (λ ())
    cn-ap _  ≟CN cn-n _ = not (λ ())
    cn-ap _  ≟CN rcn _ _  = not (λ ())
    rcn _ _  ≟CN cn-n _ = not (λ ())
    rcn _ _  ≟CN cn-ap _  = not (λ ())

    _≟PN_ : {cx cy : sCN} (x : sPN cx) (y : sPN cy) → Dec ((cx , x) ≡ (cy , y))
    _≟PN_ {cx} {cy} (pn-n x) (pn-n y) = map′ f g (eqPN x y)
      where
      f : x ≡ y → (cx , pn-n x) ≡ (cy , pn-n y)
      f refl = refl
      g : (cn-n (proj₁ (valPN x)) , pn-n x) ≡ (cn-n (proj₁ (valPN y)) , pn-n y) → x ≡ y
      g refl = refl

    _≟DET_ : (x y : sDET) → Dec (x ≡ y)
    unquoteDef _≟DET_ = defDecEq (quote sDET) _≟DET_ 

    _≟NP_ : {cx cy : sCN} (x : sNP cx) (y : sNP cy) → Dec ((cx , x) ≡ (cy , y))
    _≟NP_ {cx} {cy} (np-pn x) (np-pn y) = map′ f g (x ≟PN y )
      where
      f : (cx , x) ≡ (cy , y) → (cx , np-pn x) ≡ (cy , np-pn y)
      f refl = refl
      g : (cx , np-pn x) ≡ (cy , np-pn y) → (cx , x) ≡ (cy , y)
      g refl = refl
    _≟NP_ (np-det dx cx) (np-det dy cy) with dx ≟DET dy | cx ≟CN cy
    ... | yes dr | yes cr = yes (cong₂ (λ d c → c , np-det d c) dr cr) 
    ... | _      | not cr = not (λ z → cr (f z))
      where
      f : (cx , np-det dx cx) ≡ (cy , np-det dy cy) → cx ≡ cy
      f refl = refl
    ... | not dr | _      = not (λ z → dr (f z))
      where
      f : (cx , np-det dx cx) ≡ (cy , np-det dy cy) → dx ≡ dy
      f refl = refl
    _≟NP_ (np-pn _) (np-det _ _) = not (λ ())
    _≟NP_ (np-det _ _) (np-pn _) = not (λ ())

    _≟Adj_ : {cx cy : sCN} (x : sAdj cx) (y : sAdj cy) → Dec ((cx , x) ≡ (cy , y))
    _≟Adj_ {cx} {cy} (adj-n x) (adj-n y) = map′ f g (eqAdj x y)
      where
      f : x ≡ y → (cn-n (proj₁ (valAdj x)) , adj-n x) ≡ (cn-n (proj₁ (valAdj y)) , adj-n y)
      f refl = refl
      g : (cn-n (proj₁ (valAdj x)) , adj-n x) ≡ (cn-n (proj₁ (valAdj y)) , adj-n y) → x ≡ y
      g refl = refl

    _≟AP_ : {cx cy : sCN} (x : sAP cx) (y : sAP cy) → Dec ((cx , x) ≡ (cy , y))
    _≟AP_ {cx} {cy} (ap-a x) (ap-a y) = map′ f g (_≟Adj_ x y)
      where
      f : (cx , x) ≡ (cy , y) → (cx , ap-a x) ≡ (cy , ap-a y)
      f refl = refl
      g : (cx , ap-a x) ≡ (cy , ap-a y) → (cx , x) ≡ (cy , y)
      g refl = refl

    _≟VI_ : {cx cy : sCN} (x : sVI cx) (y : sVI cy) → Dec ((cx , x) ≡ (cy , y))
    _≟VI_ {cx} {cy} (vi-n x) (vi-n y) = map′ f g (eqVI x y)
      where
      f : x ≡ y → (cn-n (proj₁ (valVI x)) , vi-n x) ≡ (cn-n (proj₁ (valVI y)) , vi-n y)
      f refl = refl
      g : (cn-n (proj₁ (valVI x)) , vi-n x) ≡ (cn-n (proj₁ (valVI y)) , vi-n y) → x ≡ y
      g refl = refl

    _≟VT_ : {cx1 cx2 cy1 cy2 : sCN} (x : sVT cx1 cx2) (y : sVT cy1 cy2)
          → Dec ((cx1 , cx2 , x) ≡ (cy1 , cy2 , y))
    _≟VT_ {cx1} {cx2} {cy1} {cy2} (vt-n x) (vt-n y) = map′ f g (eqVT x y)
      where
      f : x ≡ y → (cx1 , cx2 , vt-n x) ≡ (cy1 , cy2 , vt-n y)
      f refl = refl
      g : (cn-n (proj₁ (valVT x)) , cn-n (proj₁ (proj₂ (valVT x))) , vt-n x)
        ≡ (cn-n (proj₁ (valVT y)) , cn-n (proj₁ (proj₂ (valVT y))) , vt-n y) → x ≡ y
      g refl = refl

    _≟VP_ : {cx cy : sCN} (x : sVP cx) (y : sVP cy) → Dec ((cx , x) ≡ (cy , y))
    _≟VP_ {cx} {cy} (vp-vi vx) (vp-vi vy) = map′ f g (vx ≟VI vy)
      where
      f : (cx , vx) ≡ (cy , vy) → (cx , vp-vi vx) ≡ (cy , vp-vi vy)
      f refl = refl
      g : (cx , vp-vi vx) ≡ (cy , vp-vi vy) → (cx , vx) ≡ (cy , vy)
      g refl = refl
      -- можно ли упростить?
    _≟VP_ {cx} {cy} (vp-vt {cx1} vtx nx) (vp-vt {cy1} vty ny)
      with cx ≟CN cy | vtx ≟VT vty | nx ≟NP ny
    ... | not ¬p | _      | _      = not \z → ¬p (f z)
      where
      f : (cx , vp-vt vtx nx) ≡ (cy , vp-vt vty ny) → cx ≡ cy
      f refl = refl
    ... | _      | not ¬p | _      = not \z → ¬p (f z)
      where
      f : (cx , vp-vt vtx nx) ≡ (cy , vp-vt vty ny) → (cx , cx1 , vtx) ≡ (cy , cy1 , vty)
      f refl = refl
    ... | _      | _      | not ¬p = not \z → ¬p (f z)
      where
      f : (cx , vp-vt vtx nx) ≡ (cy , vp-vt vty ny) → (cx1 , nx) ≡ (cy1 , ny)
      f refl = refl
    ... | yes cr | yes vtr | yes nr = map′ (f nr) (g nr) (vtx ≟VT vty)
      where
      f : (r : (cx1 , nx) ≡ (cy1 , ny)) → (cx , cx1 , vtx) ≡ (cy , cy1 , vty)
         → (cx , vp-vt vtx nx) ≡ (cy , vp-vt vty ny)
      f refl refl = refl
      g : (r : (cx1 , nx) ≡ (cy1 , ny)) → (cx , vp-vt vtx nx) ≡ (cy , vp-vt vty ny)
         → (cx , cx1 , vtx) ≡ (cy , cy1 , vty)
      g refl refl = refl
    -- _≟VP_ {cx} {cy} (vp-vt2 {cx2} vtx nx) (vp-vt2 {cy2} vty ny) with cx ≟ cy | vtx ≟VT vty | nx ≟NP ny
    -- ... | not ¬p | _      | _      = not \ z → ¬p (f z)
    --   where
    --   f : (cx , vp-vt2 vtx nx) ≡ (cy , vp-vt2 vty ny) → cx ≡ cy
    --   f refl = refl
    -- ... | _      | not ¬p | _      = not \ z → ¬p (f z)
    --   where
    --   f : (cx , vp-vt2 vtx nx) ≡ (cy , vp-vt2 vty ny) → (cx , cx2 , vtx) ≡ (cy , cy2 , vty)
    --   f refl = refl
    -- ... | _      | _      | not ¬p = not \ z → ¬p (f z)
    --   where
    --   f : (cx , vp-vt2 vtx nx) ≡ (cy , vp-vt2 vty ny) → (cx2 , nx) ≡ (cy2 , ny)
    --   f refl = refl
    -- ... | yes cr | yes vtr | yes nr = map′ (f nr) (g nr) (vtx ≟VT vty)
    --   where
    --   f : (r : (cx2 , nx) ≡ (cy2 , ny)) → (cx , cx2 , vtx) ≡ (cy , cy2 , vty)
    --      → (cx , vp-vt2 vtx nx) ≡ (cy , vp-vt2 vty ny)
    --   f refl refl = refl
    --   g : (r : (cx2 , nx) ≡ (cy2 , ny)) → (cx , vp-vt2 vtx nx) ≡ (cy , vp-vt2 vty ny)
    --      → (cx , cx2 , vtx) ≡ (cy , cy2 , vty)
    --   g refl refl = refl
    _≟VP_ (vp-vi _) (vp-vt _ _) = not (λ ())
    -- _≟VP_ (vp-vi _) (vp-vt2 _ _) = not (λ ())
    _≟VP_ (vp-vt _ _) (vp-vi _) = not (λ ())
    -- _≟VP_ (vp-vt2 _ _) (vp-vi _) = not (λ ())
    -- _≟VP_ (vp-vt1 _ _) (vp-vt2 _ _) = not (λ ())
    -- _≟VP_ (vp-vt2 _ _) (vp-vt1 _ _) = not (λ ())


  -- Определяем семантику для sCN, sPN etc.
  
  -- тип A с выделенным элементом  -- нужен для определения 'the'
  record Pointed (A : Set) : Set where
    field
      theₚ : A
  open Pointed    

  mutual
  
    ⟦scn_⟧ : sCN → Set                        -- CN ≠ e → t !  CN это тип.
    ⟦scn cn-n n ⟧ = valCN n
    ⟦scn cn-ap (ap-a (adj-n n)) ⟧ = Σ ⟦scn (cn-n (proj₁ (valAdj n))) ⟧ (proj₂ (valAdj n)) 
    ⟦scn rcn cn vp ⟧ = Σ ⟦scn cn ⟧ ⟦svp vp ⟧
    
    ⟦spn_⟧ : {cn : sCN} → sPN cn → ⟦scn cn ⟧
    ⟦spn (pn-n n) ⟧ = proj₂ (valPN n)
  
    ⟦snp_⟧ : {cn : sCN} → sNP cn → (⟦scn cn ⟧ → Set) → Set   -- NP = (e → t) → t     
    ⟦snp np-pn pn ⟧ ⟦svp⟧ = ⟦svp⟧ ⟦spn pn ⟧
    ⟦snp np-det d cn ⟧ ⟦svp⟧ = ⟦sdet d ⟧ cn ⟦svp⟧
    
    ⟦svi_⟧ : {cn : sCN} → sVI cn → ⟦scn cn ⟧ → Set           -- VI = e → t
    ⟦svi (vi-n n) ⟧ = proj₂ (valVI n)
    
    ⟦svt_⟧ : ∀ {cn1 cn} → sVT cn1 cn → ⟦scn cn1 ⟧ → ⟦scn cn ⟧ → Set    -- VT = e → e → t
    ⟦svt (vt-n n) ⟧ = proj₂ (proj₂ (valVT n)) 
  
    {-# TERMINATING #-}
    ⟦svp_⟧ : {cn : sCN} → sVP cn → ⟦scn cn ⟧ → Set             -- VP = e → t
    ⟦svp vp-vi v ⟧ = ⟦svi v ⟧ 
    ⟦svp_⟧ {cn} (vp-vt {cn1} vt np) x = ⟦snp np ⟧ λ y → ⟦svt vt ⟧ x y   -- λx.(NP (λy.(VT x y)))
  
    ⟦sdet_⟧ : sDET → (cn : sCN)→ (⟦scn cn ⟧ → Set) → Set       -- DET = (e → t) → ((e → t) → t) 
    ⟦sdet a/an ⟧  cn ⟦vp⟧ = Σ ⟦scn cn ⟧ ⟦vp⟧ 
    ⟦sdet every ⟧ cn ⟦vp⟧ = (x : ⟦scn cn ⟧) → ⟦vp⟧ x
    ⟦sdet no ⟧    cn ⟦vp⟧ = (x : ⟦scn cn ⟧) → ¬ ⟦vp⟧ x 
    ⟦sdet the ⟧   cn ⟦vp⟧ = Σ[ Aₚ ∈ Pointed ⟦scn cn ⟧ ] ⟦vp⟧ (theₚ Aₚ)
    ⟦sdet ∅ ⟧     cn ⟦vp⟧ = Σ ⟦scn cn ⟧ ⟦vp⟧
    
    ⟦sap_⟧ : {cn : sCN} → sAP cn → (⟦scn cn ⟧ → Set)           -- AP = (e → t) 
    ⟦sap ap-a (adj-n n) ⟧ = proj₂ (valAdj n)

    -- Допускаем множественную интерпретацию предложений
    ⟦ss_⟧ : sS → List Set
    ⟦ss s-nv np vp ⟧ = ⟦snp np ⟧ ⟦svp vp ⟧ ∷ []
    ⟦ss s-nvn np1 vt np2 ⟧ = ⟦snp np1 ⟧ (λ x → (⟦snp np2 ⟧ λ y → ⟦svt vt ⟧ x y)) 
                           ∷ ⟦snp np2 ⟧ (λ x → (⟦snp np1 ⟧ λ y → ⟦svt vt ⟧ y x))
                           ∷ []

    -- проверим равенство
    _ : ∀ {cn1 cn2} {np1 : sNP cn1}{np2 : sNP cn2}{vt : sVT cn1 cn2} →
        (⟦snp np1 ⟧ (λ x → (⟦snp np2 ⟧ λ y → ⟦svt vt ⟧ x y))) ≡ (⟦snp np1 ⟧ ⟦svp vp-vt vt np2 ⟧)
    _ = refl


  -- перевод из CN, PN,... в sCN, sPN,...
  -- перевод не всегда существует, поэтому -- Maybe
  
  mutual
  
    fCN : CN → Maybe sCN
    fCN (cn-n x) = just $ cn-n x
    fCN (cn-ap x)  = just $ cn-ap $ proj₂ $ fAP x 
    fCN (rcn cn vp) with fCN cn | fVP vp
    ...             | just cn' | just vp' with cn' ≟CN (proj₁ vp')
    ...                                   | yes r = just $ rcn cn' (subst sVP (sym r) (proj₂ vp'))
    ...                                   | not _ = nothing
    fCN (rcn cn vp) | _ | _ = nothing

    fPN : PN → Σ[ cn ∈ sCN ] (sPN cn)
    fPN (pn-n x) = cn-n (proj₁ (valPN x)) , pn-n x

    fVI : VI → Σ[ cn ∈ sCN ] (sVI cn)
    fVI (vi-n x) = cn-n (proj₁ (valVI x)) , vi-n x 

    fVT : VT → Σ[ cn1 ∈ sCN ] Σ[ cn2 ∈ sCN ] (sVT cn1 cn2)
    fVT (vt-n x) = (cn-n (proj₁ (valVT x))) , (cn-n (proj₁ (proj₂ (valVT x)))) , (vt-n x)

    fAdj : Adj → Σ[ cn ∈ sCN ] (sAdj cn)
    fAdj (adj-n x) = (cn-n (proj₁ (valAdj x))) , (adj-n x)

    fDET : DET → sDET
    fDET a/an = a/an
    fDET every = every
    fDET no = no
    fDET the = the
    fDET ∅ = ∅

    fNP : NP → Maybe (Σ[ cn ∈ sCN ] (sNP cn))
    fNP (np-pn (pn-n x)) = just $ cn-n (proj₁ (valPN x)) , np-pn (pn-n x)
    fNP (np-det d c) with fCN c
    ... | just x = just $ x , (np-det (fDET d) x)
    ... | nothing = nothing

    fVP : VP → Maybe (Σ[ cn ∈ sCN ] (sVP cn))
    fVP (vp-vi (vi-n x)) = just $ proj₁ (fVI (vi-n x)) , vp-vi (vi-n x)
    fVP (vp-vt vt np) with fNP np
    ... | nothing = nothing
    ... | just np' with (proj₁ (proj₂ (fVT vt))) ≟CN (proj₁ np')
    ...                 | yes r  = just $ (proj₁ (fVT vt))
                                          , (vp-vt (proj₂ (proj₂ (fVT vt))) (subst sNP (sym r) (proj₂ np')))
    ...                 | not _ = nothing
    -- fVP (vp-vt2 vt np) with fNP np
    -- ... | nothing = nothing
    -- ... | just np' with (proj₁ (proj₂ (fVT vt))) ≟ (proj₁ np')
    -- ...                 | yes r  = just $ (proj₁ (fVT vt))
    --                                       , (vp-vt2 (proj₂ (proj₂ (fVT vt))) (subst sNP (sym r) (proj₂ np')))
    -- ...                 | not _ = nothing

    fAP : AP → Σ[ cn ∈ sCN ] sAP cn
    fAP (ap-a (adj-n x)) = cn-n (proj₁ (valAdj x)) , ap-a (adj-n x)

    fS : S → Maybe sS
    fS (s-nv np vp) with fNP np | fVP vp
    ... | just np' | just vp' with (proj₁ np') ≟CN (proj₁ vp')
    ...                        | yes r = just $ s-nv (proj₂ np') (subst sVP (sym r) (proj₂ vp'))
    ...                        | not _ = nothing
    fS (s-nv np vp) | _ | _ = nothing
    fS (s-nvn np1 vt np2) with fNP np1 | fVT vt | fNP np2
    ...  | just np1' | cn1 , cn2 , vt' | just np2' with proj₁ np1' ≟CN cn1 | proj₁ np2' ≟CN cn2
    ...                                            | yes r1 | yes r2 =
                                                        just $ s-nvn (proj₂ np1')
                                                                     (subst (λ z → sVT z cn2) (sym r1) vt')
                                                                     (subst sNP r2 (proj₂ np2'))
    ...                                            | _      | _      = nothing
    fS (s-nvn np1 vt np2) | _ | _ | _ = nothing


  -- Семантика для CN, PN,...

  -- я здесь использую ⊥ вместо nothing, это немного удобнее для вычислений
  ⟦cn_⟧ : CN → Set
  ⟦cn c ⟧ with fCN c
  ... | just sc = ⟦scn sc ⟧
  ... | nothing = ⊥
  
  ⟦pn_⟧ : PN → Σ[ cn ∈ sCN ] ⟦scn cn ⟧
  ⟦pn n ⟧ = let (sc , sn) = fPN n in sc , ⟦spn sn ⟧   
  
  ⟦np_⟧ : NP → Maybe (Σ[ cn ∈ sCN ] ((⟦scn cn ⟧ → Set) → Set))
  ⟦np n ⟧ with fNP n
  ... | just (cn , sn) = just (cn , ⟦snp sn ⟧)
  ... | nothing = nothing
  
  ⟦vi_⟧ : VI → Σ[ scn ∈ sCN ] (⟦scn scn ⟧ → Set)
  ⟦vi vi ⟧ = let (sc , sv) = fVI vi in sc , ⟦svi sv ⟧
  
  ⟦vt_⟧ : VT → Σ[ scn1 ∈ sCN ] Σ[ scn2 ∈ sCN ] (⟦scn scn1 ⟧ → ⟦scn scn2 ⟧ → Set)
  ⟦vt vt ⟧ = let (cn1 , cn2 , svt) = fVT vt in cn1 , cn2 , ⟦svt svt ⟧
  
  ⟦vp_⟧ : VP → Maybe (Σ[ scn ∈ sCN ] (⟦scn scn ⟧ → Set))
  ⟦vp vp ⟧ with fVP vp
  ... | just (scn , svp) = just (scn , ⟦svp svp ⟧)
  ... | nothing = nothing
  
  ⟦det_⟧ : DET → (cn : sCN) → (⟦scn cn ⟧ → Set) → Set
  ⟦det d ⟧ = ⟦sdet (fDET d) ⟧
  
  ⟦ap_⟧ : AP → Σ[ scn ∈ sCN ] (⟦scn scn ⟧ → Set)
  ⟦ap ap ⟧ = let (sc , sa) = fAP ap in sc , ⟦sap sa ⟧

  -- также допускаем множественные интерпретации
  ⟦s_⟧ : S → List Set
  ⟦s s ⟧ with fS s
  ... | just ss = ⟦ss ss ⟧
  ... | nothing = []


-- Примеры

data namePN  : Set where Mary Alex Polkan : namePN
data nameCN  : Set where Human Dog : nameCN
data nameVI  : Set where runs : nameVI
data nameVT  : Set where love : nameVT
data nameAdj : Set where black : nameAdj

postulate
  *Human *Dog : Set
  *Alex *Mary : *Human
  *Polkan : *Dog
  _*runs : *Human → Set
  _*love_ : *Human → *Human → Set
  *black : *Dog → Set 

-- разрешимое равенство для имён

eqCN : (x y : nameCN) → Dec (x ≡ y)
unquoteDef eqCN = defDecEq (quote nameCN) eqCN 

eqPN : (x y : namePN) → Dec (x ≡ y)
unquoteDef eqPN = defDecEq (quote namePN) eqPN 

eqVI : (x y : nameVI) → Dec (x ≡ y)
eqVI runs runs = yes refl

eqVT : (x y : nameVT) → Dec (x ≡ y)
eqVT love love = yes refl

eqAdj : (x y : nameAdj) → Dec (x ≡ y)
eqAdj black black = yes refl

NS : LexStructure
NS = record
       { nameCN = nameCN 
       ; namePN = namePN 
       ; nameVI = nameVI 
       ; nameVT = nameVT 
       ; nameAdj = nameAdj
       ; eqCN =  eqCN  
       ; eqPN =  eqPN  
       ; eqVI =  eqVI  
       ; eqVT =  eqVT  
       ; eqAdj = eqAdj 
       }

-- валюация для имён

valCN : nameCN → Set
valCN Human = *Human
valCN Dog = *Dog

valPN : namePN → Σ[ cn ∈ nameCN ] (valCN cn) 
valPN Mary = Human , *Mary
valPN Alex = Human , *Alex
valPN Polkan = Dog , *Polkan

valVI : nameVI → Σ[ cn ∈ nameCN ] (valCN cn → Set)
valVI runs = Human , _*runs

valVT : nameVT → Σ[ cn1 ∈ nameCN ] Σ[ cn2 ∈ nameCN ] (valCN cn1 → valCN cn2 → Set)
valVT love = Human , Human , _*love_

valAdj : nameAdj → Σ[ cn ∈ nameCN ] (valCN cn → Set)
valAdj black = Dog , *black

M : Model NS
M = record { valCN  = valCN
           ; valPN  = valPN
           ; valVI  = valVI
           ; valVT  = valVT
           ; valAdj = valAdj
           }
  
open Semantics NS M 


_ : fPN (pn-n Mary) ≡ (cn-n Human , pn-n Mary)
_ = refl

_ : NP
_ = np-pn (pn-n Mary)

_ : ⟦vi (vi-n runs) ⟧ ≡ (cn-n Human , _*runs)
_ = refl

_ : ⟦vt (vt-n love) ⟧ ≡ (cn-n Human , cn-n Human , _*love_)
_ = refl

_ : ⟦vp (vp-vi (vi-n runs)) ⟧ ≡ just (cn-n Human , _*runs)
_ = refl

_ : ⟦pn (pn-n Mary) ⟧ ≡ (cn-n Human , *Mary)
_ = refl

_ : ⟦np (np-pn (pn-n Mary)) ⟧ ≡ just (cn-n Human , λ vp → vp *Mary)
_ = refl


-- Mary runs
s1 : S
s1 = s-nv (np-pn (pn-n Mary)) (vp-vi (vi-n runs))

_ : fS s1 ≡ (just (s-nv (np-pn (pn-n Mary)) (vp-vi (vi-n runs))))
_ = refl 

_ : ⟦s s1 ⟧ ≡ (*Mary *runs) ∷ []
_ = refl


-- Polkan runs
s2 : S
s2 = s-nv (np-pn (pn-n Polkan)) (vp-vi (vi-n runs))

_ : ⟦s s2 ⟧ ≡ []   -- s2 семантически некорректно, хотя синтаксически правильно
_ = refl


-- a human runs
s4 : S
s4 = s-nv (np-det a/an (cn-n Human)) (vp-vi (vi-n runs))

_ : ⟦s s4 ⟧ ≡ (Σ[ x ∈ *Human ] x *runs) ∷ []
_ = refl


-- every human runs
s5 : S
s5 = s-nv (np-det every (cn-n Human)) (vp-vi (vi-n runs))

_ : ⟦s s5 ⟧ ≡ ((x : *Human) → x *runs) ∷ []
_ = refl


-- the human runs
s6 : S
s6 = s-nv (np-det the (cn-n Human)) (vp-vi (vi-n runs))

-- вспомогательные функции
inhabited : ∀ {a} {A : Set a} → List A → Set
inhabited [] = ⊥
inhabited _  = ⊤

head : ∀ {a}{A : Set a} → (l : List A) → {inhabited l} → A
head (x ∷ _) = x   


pp : head ⟦s s6 ⟧
pp = Hₚ , *Mary-runs
  where
  Hₚ : Pointed *Human 
  Hₚ = record { theₚ = *Mary }

  postulate *Mary-runs : *Mary *runs




-- Прилагательные / свойства


black-dog : ⟦cn cn-ap (ap-a (adj-n black)) ⟧      -- здесь ⊥ в ⟦cn_⟧ удобнее, чем nothing
black-dog = *Polkan , *polkan-is-black
  where
  postulate *polkan-is-black : *black *Polkan



-- Относительные конструкции (CN that VP и пр.)

human-that-runs : CN
human-that-runs = rcn (cn-n Human) (vp-vi (vi-n runs))

_ : ⟦cn human-that-runs ⟧
_ = *Mary , *Mary-runs
  where
  postulate *Mary-runs : *Mary *runs 


a-human-that-runs : NP  
a-human-that-runs = np-det a/an human-that-runs



-- Ещё примеры предложений --

-- Mary loves Alex

s11 : S
s11 = s-nv (np-pn (pn-n Mary)) (vp-vt (vt-n love) (np-pn (pn-n Alex)))

_ : ⟦s s11 ⟧ ≡ *Mary *love *Alex ∷ []
_ = refl


-- Mary loves a/an human

s12 : S
s12 = s-nv (np-pn (pn-n Mary)) (vp-vt (vt-n love) (np-det a/an (cn-n Human)))

_ : ⟦s s12 ⟧ ≡ (Σ[ x ∈ *Human ] (*Mary *love x)) ∷ []
_ = refl

_ : head ⟦s s12 ⟧
_ = *Alex , *Mary-loves-Alex
  where
  postulate *Mary-loves-Alex : *Mary *love *Alex


-- Every human loves a human (different)

s13 : S
s13 = s-nv (np-det every (cn-n Human)) (vp-vt (vt-n love) (np-det a/an (cn-n Human)))

_ : ⟦s s13 ⟧ ≡ (∀(x : *Human) → Σ[ y ∈ *Human ] x *love y) ∷ []
_ = refl



-- Двусмысленность:
-- Every human loves a human

s17 : S
s17 = s-nvn (np-det every (cn-n Human)) (vt-n love) (np-det a/an (cn-n Human))

_ : ⟦s s17 ⟧ ≡ (∀(x : *Human) → Σ[ y ∈ *Human ] x *love y)          -- ср. s13
             ∷ (Σ[ y ∈ *Human ] ∀ (x : *Human) → x *love y)         -- all x love the same y
             ∷ []
_ = refl


-- НО!
-- Два смысла предложения могут и совпадать:

s18 : S
s18 = s-nvn (np-pn (pn-n Mary)) (vt-n love) (np-pn (pn-n Alex))

_ : ⟦s s18 ⟧ ≡ (*Mary *love *Alex)
             ∷ (*Mary *love *Alex)
             ∷ []
_ = refl            
