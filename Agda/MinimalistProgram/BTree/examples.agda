module BTree.examples where

open import Data.Bool using (Bool; true; false)
-- open import Data.Fin hiding (_-_)
open import Data.Maybe
open import Data.Nat hiding (_>_)
open import Data.List as 𝕃 hiding ([_]; foldr; foldl)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import BTree.SyntaxObject

module ex9 where

  -- That I care proves everything  -- cf. Adger, p.246

  -- first, "that I care"

  thatˡⁱ = mkLI ("that" ∷ []) [] (Cᶠ ∷ []) (Tᶠ ∷ [])
  Iˡⁱ    = mkLI ("I" ∷ [])    [] (N ∷ [])  []
  careˡⁱ = mkLI ("care" ∷ []) [] (V ∷ [])  []
  vˡⁱ    = mkLI ("v" ∷ [])    [] (vᶠ ∷ []) (V ∷ N ∷ [])
  Tˡⁱ    = mkLI ("T" ∷ [])    [] (Tᶠ ∷ []) (vᶠ ∷ N ∷ [])
  Cˡⁱ    = mkLI ("C" ∷ [])    [] (Cᶠ ∷ []) (Tᶠ ∷ [])

  thatˡᵃ Iˡᵃ careˡᵃ vˡᵃ Tˡᵃ : LexArr

  thatˡᵃ = [ thatˡⁱ ]
  Iˡᵃ    = Iˡⁱ ∷ thatˡᵃ
  careˡᵃ = careˡⁱ ∷ Iˡᵃ
  vˡᵃ    = vˡⁱ ∷ careˡᵃ
  Tˡᵃ    = Tˡⁱ ∷ vˡᵃ

  that = ⟦ thatˡᵃ ⟧
  I    = ⟦ Iˡᵃ ⟧
  care = ⟦ careˡᵃ ⟧
  v    = ⟦ vˡᵃ ⟧
  T    = ⟦ Tˡᵃ ⟧

  dtc = Merge (Select thatˡᵃ)
              (Merge (Select Iˡᵃ)
                     (Merge (Select Tˡᵃ)
                            (Merge (Select Iˡᵃ)
                                   (Merge (Select vˡᵃ)
                                          (Select careˡᵃ)))))

  soc = DTree→SO dtc

  _ : soc ≡ ⟦ ("that" ∷ []) ∙ [] ∙ (Cᶠ ∷ []) ∙ []
              - that
              - ⟦ ("T" ∷ []) ∙ [] ∙ (Tᶠ ∷ []) ∙ []
                  - I
                  - ⟦ ("T" ∷ []) ∙ [] ∙ (Tᶠ ∷ []) ∙ (N ∷ [])
                      - T
                      - ⟦ ("v" ∷ []) ∙ [] ∙ (vᶠ ∷ []) ∙ []
                          - I
                          - ⟦ ("v" ∷ []) ∙ [] ∙ (vᶠ ∷ []) ∙ (N ∷ [])
                              - v
                              - care ⟧ ⟧ ⟧ ⟧ ⟧
  _ = refl                              
  

  -- now the full sentence

  proveˡⁱ      = mkLI ("prove" ∷ [])      [] (V ∷ [])  (N ∷ [])
  everythingˡⁱ = mkLI ("everything" ∷ []) [] (N ∷ [])  []
  v2ˡⁱ         = mkLI ("v" ∷ [])          [] (vᶠ ∷ []) (V ∷ Cᶠ ∷ [])
  T2ˡⁱ         = mkLI ("T" ∷ [])          [] (Tᶠ ∷ []) (vᶠ ∷ Cᶠ ∷ [])

  proveˡᵃ everythingˡᵃ v2ˡᵃ T2ˡᵃ C2ˡᵃ : LexArr

  proveˡᵃ      = proveˡⁱ ∷ Tˡᵃ
  everythingˡᵃ = everythingˡⁱ ∷ proveˡᵃ
  v2ˡᵃ         = v2ˡⁱ ∷ everythingˡᵃ
  T2ˡᵃ         = T2ˡⁱ ∷ v2ˡᵃ
  C2ˡᵃ         = Cˡⁱ ∷ T2ˡᵃ

  prove      = ⟦ proveˡᵃ ⟧
  everything = ⟦ everythingˡᵃ ⟧
  v2         = ⟦ v2ˡᵃ ⟧
  T2         = ⟦ T2ˡᵃ ⟧
  C2         = ⟦ C2ˡᵃ ⟧

  dt = Merge (Select C2ˡᵃ)
             (Merge dtc
                    (Merge (Select T2ˡᵃ)
                           (Merge dtc
                                  (Merge (Select v2ˡᵃ)
                                         (Merge (Select proveˡᵃ)
                                                (Select everythingˡᵃ))))))

  so = DTree→SO dt

  _ : so ≡ ⟦ ("C" ∷ []) ∙ [] ∙ (Cᶠ ∷ []) ∙ []
             - C2
             - ⟦ ("T" ∷ []) ∙ [] ∙ (Tᶠ ∷ []) ∙ []
                 - soc
                 - ⟦ ("T" ∷ []) ∙ [] ∙ (Tᶠ ∷ []) ∙ (Cᶠ ∷ [])
                     - T2
                     - ⟦ ("v" ∷ []) ∙ [] ∙ (vᶠ ∷ []) ∙ []
                         - soc
                         - ⟦ ("v" ∷ []) ∙ [] ∙ (vᶠ ∷ []) ∙ (Cᶠ ∷ [])
                             - v2
                             - ⟦ ("prove" ∷ []) ∙ [] ∙ (V ∷ []) ∙ []
                                 - prove
                                 - everything ⟧ ⟧ ⟧ ⟧ ⟧ ⟧
  _ = refl                                 

  dt0 = Merge (Select proveˡᵃ) (Select everythingˡᵃ)
  dt1 = Merge (Select v2ˡᵃ) dt0
  dt2 = Merge dtc dt1
  dt3 = Merge (Select T2ˡᵃ) dt2
  dt4 = Merge dtc dt3
  so0 = DTree→SO dt0
  so1 = DTree→SO dt1
  so2 = DTree→SO dt2
  so3 = DTree→SO dt3
  so4 = DTree→SO dt4


  _ : chainL soc so ≡ (so ∷ so4 ∷ soc ∷ [])
                    ∷ (so ∷ so4 ∷ so3 ∷ so2 ∷ soc ∷ [])
                    ∷ []
  _ = refl


--========================================================================

module ex8 where

  li1 li2 li3 : LexItem
  li1 = mkLI ("li1" ∷ []) [] [] [] 
  li2 = mkLI ("li2" ∷ []) [] [] [] 
  li3 = mkLI ("li3" ∷ []) [] [] [] 


  l1 l2 l3 : LexArr
  l1 = [ li1 ]
  l2 = li2 ∷ l1
  l3 = li3 ∷ l2

  s1 = Select l1
  s2 = Select l2
  s3 = Select l3
  s0 = Merge s1 s2   -- ⟦ s1 - s2 ⟧

  so0 = DTree→SO s0
  so1 = DTree→SO s1
  so2 = DTree→SO s2
  so3 = DTree→SO s3
  
  p0-1 : so0 contains so1
  p0-1 = c0 cl 

  _ : Path→List p0-1 ≡ so0 ∷ so1 ∷ []
  _ = refl

  p0-2 : so0 contains so2
  p0-2 = c0 cr

  p1-1 : so1 contains so1
  p1-1 = c0
  
  p2-2 : so2 contains so2
  p2-2 = c0
  
  s3l = Merge s0 s3
  so3l = DTree→SO s3l

  p3l-1 : so3l contains so1
  p3l-1 = c0 cl cl

  _ : Path→List p3l-1 ≡ so3l ∷ so0 ∷ so1 ∷ []
  _ = refl

  s3r = Merge s3 s0  
  so3r = DTree→SO s3r

  _ : s3r ≡ Merge s3
                   (Merge s1
                           s2)
  _ = refl
  
  _ : so3r ≡ ⟦ LMerge (lbl so3) (LMerge (lbl so1) (lbl so2))
                      - so3
                      - ⟦ LMerge (lbl so1) (lbl so2)
                            - so1
                            - so2 ⟧ ⟧
  _ = refl
  
  p3r-1 : so3r contains so1
  p3r-1 = c0 cr cl

  _ : Path→List p3r-1 ≡ so3r ∷ so0 ∷ so1 ∷ []
  _ = refl

  _ : s3r ≡ Merge s3
                  (Merge s1 s2)
  _ = refl
  
  -- internal Merge
  s4 = Merge s1 s0
  so4 = DTree→SO s4

  _ : so4 ≡ ⟦ "li2" ∷ [] ∙ [] ∙ [] ∙ []  --LMerge (lbl so1) (LMerge (lbl so1) (lbl so2))
              - so1
              - ⟦ LMerge (lbl so1) (lbl so2)
                  - so1
                  - so2 ⟧ ⟧
  _ = refl
  
  p4-0 : so4 contains so0
  p4-0 = c0 cr

  p4-1 : so4 contains so1
  p4-1 = c0 cl

  p4-0-1 : so4 contains so1
  p4-0-1 = c0 cr cl

  p4-0-2 : so4 contains so2
  p4-0-2 = c0 cr cr 

  _ : Path→List p4-1 ≡ so4 ∷ so1 ∷ []
  _ = refl

  _ : Path→List p4-0-1 ≡ so4 ∷ so0 ∷ so1 ∷ []
  _ = refl

  _ : internalMerge? so3r ≡ false
  _ = refl

  _ : internalMerge? so4 ≡ true
  _ = refl
  


  _ : nodesNum so1 ≡ 1
  _ = refl

  _ : nodesNum so0 ≡ 3
  _ = refl

  _ : nodesNum so4 ≡ 5
  _ = refl


  _ : edgesNum so1 ≡ 0
  _ = refl

  _ : edgesNum so0 ≡ 2
  _ = refl

  _ : edgesNum so4 ≡ 4
  _ = refl



  -- constituents
  _ : Constituents so2 ≡ so2 ∷ []
  _ = refl

  _ : Constituents so0 ≡ so0 ∷ so1 ∷ so2 ∷ []
  _ = refl

  _ : Constituents so3r ≡ so3r ∷ so3 ∷ so0 ∷ so1 ∷ so2 ∷ []
  _ = refl



  -- positions

  _ : positions so1 ≡ (pos c0) ∷ []
  _ = refl

  _ : positions so0 ≡ pos c0
                    ∷ pos (c0 cl)
                    ∷ pos (c0 cr) ∷ []
  _ = refl

  _ : positions so4 ≡ pos c0
                    ∷ pos (c0 cl)
                    ∷ pos (c0 cr)
                    ∷ pos (c0 cr cl)
                    ∷ pos (c0 cr cr) ∷ []
  _ = refl

  
  _ : positionsSO so1 ≡ (so1 ∷ []) ∷ []
  _ = refl

  _ : positionsSO so2 ≡ (so2 ∷ []) ∷ []
  _ = refl

  _ : positionsSO so0 ≡ (so0 ∷ []) 
                     ∷ (so0 ∷ so1 ∷ []) 
                     ∷ (so0 ∷ so2 ∷ []) 
                     ∷ []
  _ = refl          
                    
  _ : positionsSO so4 ≡ (so4 ∷ [])
                     ∷ (so4 ∷ so1 ∷ [])
                     ∷ (so4 ∷ so0 ∷ [])
                     ∷ (so4 ∷ so0 ∷ so1 ∷ [])
                     ∷ (so4 ∷ so0 ∷ so2 ∷ [])
                     ∷ []
  _ = refl

  _ : positionsSO' so4 ≡ positionsSO so4
  _ = refl


  _ : chainL so1 so1 ≡ (so1 ∷ []) ∷ []
  _ = refl

  _ : chainL so1 so0 ≡ (so0 ∷ so1 ∷ [])
                    ∷ []
  _ = refl

  _ : chainL so1 so4 ≡ (so4 ∷ so1 ∷ [])
                    ∷ (so4 ∷ so0 ∷ so1 ∷ [])
                    ∷ []
  _ = refl

  _ : chainL so0 so4 ≡ (so4 ∷ so0 ∷ [])
                    ∷ []
  _ = refl

  _ : chainL so2 so4 ≡ (so4 ∷ so0 ∷ so2 ∷ [])
                    ∷ []
  _ = refl



  pp0 : Position so1
  pp0 = pos c0

  pp1 : Position so0
  pp1 = pos p0-1

  pp2 : Position so0
  pp2 = pos p0-2

  _ : Pos→List pp0 ≡ so1 ∷ []
  _ = refl

  _ : Pos→List pp1 ≡ so0 ∷ so1 ∷ []
  _ = refl

  _ : Pos→List pp2 ≡ so0 ∷ so2 ∷ []
  _ = refl


  pp41 : Position so4
  pp41 = pos p4-1

  _ : Pos→List pp41 ≡ so4 ∷ so1 ∷ []
  _ = refl

  _ : Pos→SO pp41 ≡ so1
  _ = refl

  pp42 : Position so4
  pp42 = pos {so4} p4-0-1      -- ???

  _ : Pos→List pp42 ≡ so4 ∷ so0 ∷ so1 ∷ []
  _ = refl

  _ : Pos→SO pp42 ≡ so1
  _ = refl


  -- concatenation

  _ : p0-2 > p2-2 ≡ p0-2
  _ = refl
  
  _ : p4-0 > p0-1 ≡ p4-0-1
  _ = refl

  _ : p3l-1 > p1-1 ≡ p3l-1
  _ = refl



  -- c-command

  _ : c-commanded pp0 ≡ []
  _ = refl
  
  _ : c-commanded pp1 ≡ pos (c0 cr) ∷ []
  _ = refl

  _ : c-commanded pp41 ≡ pos (c0 cr)
                       ∷ pos (c0 cr cl)
                       ∷ pos (c0 cr cr) ∷ []
  _ = refl

  _ : 𝕃.map Pos→List (c-commanded pp41) ≡ (so4 ∷ so0 ∷ [])
                                        ∷ (so4 ∷ so0 ∷ so1 ∷ [])
                                        ∷ (so4 ∷ so0 ∷ so2 ∷ [])
                                        ∷ []
  _ = refl                                        


--========================================================================

-- module ex7 where

  -- John seeks a unicorn



--========================================================================

module ex6 where

  -- Which picture of himself Peter loves?

  pictureˡⁱ    = mkLI ("picture" ∷ []) [] (N ∷ []) (P ∷ [])
  Peterˡⁱ      = mkLI ("Peter" ∷ []) [] (N ∷ []) []
  loveˡⁱ       = mkLI ("love" ∷ []) [] (V ∷ []) (Wh:* ∷ N ∷ [])
  of-himselfˡⁱ = mkLI ("of-himself" ∷ []) [] (P ∷ []) []
  whichˡⁱ      = mkLI ("which" ∷ []) [] (Wh:* ∷ []) (N ∷ [])

  pictureˡᵃ of-himselfˡᵃ Peterˡᵃ loveˡᵃ whichˡᵃ : LexArr
  pictureˡᵃ    = [ pictureˡⁱ ] 
  of-himselfˡᵃ = of-himselfˡⁱ ∷ pictureˡᵃ
  Peterˡᵃ      = Peterˡⁱ ∷ of-himselfˡᵃ
  loveˡᵃ       = loveˡⁱ ∷ Peterˡᵃ
  whichˡᵃ      = whichˡⁱ ∷ loveˡᵃ

  picture    = ⟦ pictureˡᵃ ⟧
  of-himself = ⟦ of-himselfˡᵃ ⟧
  Peter      = ⟦ Peterˡᵃ ⟧
  love       = ⟦ loveˡᵃ ⟧
  which      = ⟦ whichˡᵃ ⟧

  dtw = Merge (Select whichˡᵃ)
              (Merge (Select of-himselfˡᵃ)
                     (Select pictureˡᵃ))
                     
  dt = Merge dtw
             (Merge (Select Peterˡᵃ)
                    (Merge (Select loveˡᵃ)
                           dtw))

  sow = DTree→SO dtw
  so = DTree→SO dt

  _ : so ≡ ⟦ ("love" ∷ []) ∙ [] ∙ V ∷ [] ∙ []  --("which" ∷ []) ∙ [] ∙ Wh:* ∷ [] ∙ []  
             - ⟦ ("which" ∷ []) ∙ [] ∙ Wh:* ∷ [] ∙ []
                 - which
                 - ⟦ ("picture" ∷ []) ∙ [] ∙ N ∷ [] ∙ []
                     - of-himself
                     - picture ⟧ ⟧ 
             - ⟦ ("love" ∷ []) ∙ [] ∙ V ∷ [] ∙ []
                 - Peter
                 - ⟦ ("love" ∷ []) ∙ [] ∙ V ∷ [] ∙ N ∷ []
                     - love
                     - ⟦ ("which" ∷ []) ∙ [] ∙ Wh:* ∷ [] ∙ []
                         - which
                         - ⟦ ("picture" ∷ []) ∙ [] ∙ N ∷ [] ∙ []
                             - of-himself
                             - picture ⟧ ⟧ ⟧ ⟧ ⟧
  _ = refl                             


  _ : internalMerge? so ≡ true
  _ = refl

  _ : internalMerge? sow ≡ false
  _ = refl


  -- wrong tree

  so-wrong = DTree→SO (Merge (Select Peterˡᵃ) (Select pictureˡᵃ))

  _ : so-wrong ≡ ⟦ nothing - Peter - picture ⟧
  _ = refl             

  dt0 = Merge (Select of-himselfˡᵃ) (Select pictureˡᵃ)
  dt1 = Merge (Select loveˡᵃ) dtw
  dt2 = Merge (Select Peterˡᵃ) dt1
  so0 = DTree→SO dt0
  so1 = DTree→SO dt1
  so2 = DTree→SO dt2

  _ : positions so ≡ pos c0 
                   ∷ pos (c0 cl) 
                   ∷ pos (c0 cl cl) 
                   ∷ pos (c0 cl cr) 
                   ∷ pos (c0 cl cr cl) 
                   ∷ pos (c0 cl cr cr) 
                   ∷ pos (c0 cr) 
                   ∷ pos (c0 cr cl) 
                   ∷ pos (c0 cr cr) 
                   ∷ pos (c0 cr cr cl) 
                   ∷ pos (c0 cr cr cr) 
                   ∷ pos (c0 cr cr cr cl) 
                   ∷ pos (c0 cr cr cr cr) 
                   ∷ pos (c0 cr cr cr cr cl)
                   ∷ pos (c0 cr cr cr cr cr)
                   ∷ []
  _ = refl

  _ : positionsSO sow ≡ (sow ∷ [])
                     ∷ (sow ∷ which ∷ [])
                     ∷ (sow ∷ so0 ∷ [])
                     ∷ (sow ∷ so0 ∷ of-himself ∷ [])
                     ∷ (sow ∷ so0 ∷ picture ∷ [])
                     ∷ []
  _ = refl

  _ : positionsSO so ≡ (so ∷ [])
                    ∷ (so ∷ sow ∷ [])
                    ∷ (so ∷ sow ∷ which ∷ [])
                    ∷ (so ∷ sow ∷ so0 ∷ [])
                    ∷ (so ∷ sow ∷ so0 ∷ of-himself ∷ [])
                    ∷ (so ∷ sow ∷ so0 ∷ picture ∷ [])
                    ∷ (so ∷ so2 ∷ [])
                    ∷ (so ∷ so2 ∷ Peter ∷ [])
                    ∷ (so ∷ so2 ∷ so1 ∷ [])
                    ∷ (so ∷ so2 ∷ so1 ∷ love ∷ [])
                    ∷ (so ∷ so2 ∷ so1 ∷ sow ∷ [])
                    ∷ (so ∷ so2 ∷ so1 ∷ sow ∷ which ∷ [])
                    ∷ (so ∷ so2 ∷ so1 ∷ sow ∷ so0 ∷ [])
                    ∷ (so ∷ so2 ∷ so1 ∷ sow ∷ so0 ∷ of-himself ∷ [])
                    ∷ (so ∷ so2 ∷ so1 ∷ sow ∷ so0 ∷ picture ∷ [])
                    ∷ []
  _ = refl

  _ : chainL sow so ≡ (so ∷ sow ∷ [])
                    ∷ (so ∷ so2 ∷ so1 ∷ sow ∷ [])
                    ∷ []
  _ = refl                   


--========================================================================

module ex51 where
  
  -- vP: Маша ела кашу.   -- simplified a little
  
  Машаˡⁱ      = mkLI ("Маша" ∷ []) [] (N ∷ fem ∷ [])       []
  елаˡⁱ       = mkLI ("ела" ∷ [])  [] (V ∷ past ∷ [])      (N ∷ [])
  кашуˡⁱ      = mkLI ("кашу" ∷ []) [] (N ∷ fem ∷ ACC ∷ []) []
  vˡⁱ         = mkLI ("v" ∷ [])    [] (vᶠ ∷ [])            (V ∷ N ∷ [])
  
  елаˡᵃ vˡᵃ Машаˡᵃ кашуˡᵃ : LexArr
  елаˡᵃ  = [ елаˡⁱ ]
  vˡᵃ    = vˡⁱ ∷ елаˡᵃ
  Машаˡᵃ = Машаˡⁱ ∷ vˡᵃ
  кашуˡᵃ = кашуˡⁱ ∷ Машаˡᵃ
  
  Маша      = ⟦ Машаˡᵃ ⟧
  ела       = ⟦ елаˡᵃ ⟧
  кашу      = ⟦ кашуˡᵃ ⟧
  v         = ⟦ vˡᵃ ⟧

  dtv = Merge (Select vˡᵃ)
              (Merge (Select елаˡᵃ)
                     (Select кашуˡᵃ))
                     
  dt = Merge (Select Машаˡᵃ) dtv

  sov = DTree→SO dtv
  so = DTree→SO dt

  _ : sov ≡ ⟦ ("v" ∷ []) ∙ [] ∙ vᶠ ∷ [] ∙ N ∷ [] 
              - v 
              - ⟦ ("ела" ∷ []) ∙ [] ∙ V ∷ past ∷ [] ∙ []  
                  - ела 
                  - кашу ⟧ ⟧
  _ = refl                             

  _ : so ≡ ⟦ ("v" ∷ []) ∙ [] ∙ vᶠ ∷ [] ∙ []
             - Маша
             - ⟦ ("v" ∷ []) ∙ [] ∙ vᶠ ∷ [] ∙ N ∷ [] 
                 - v 
                 - ⟦ ("ела" ∷ []) ∙ [] ∙ V ∷ past ∷ [] ∙ []  
                     - ела 
                     - кашу ⟧ ⟧ ⟧
  _ = refl             


  _ : Constituents so ≡ so
                      ∷ Маша
                      ∷ ⟦ ("v" ∷ []) ∙ [] ∙ vᶠ ∷ [] ∙ N ∷ [] 
                          - v 
                          - ⟦ ("ела" ∷ []) ∙ [] ∙ V ∷ past ∷ [] ∙ []  
                              - ела 
                              - кашу ⟧ ⟧
                     ∷ v
                     ∷ ⟦ ("ела" ∷ []) ∙ [] ∙ V ∷ past ∷ [] ∙ []  
                         - ела 
                         - кашу ⟧
                     ∷ ела
                     ∷ кашу
                     ∷ []
  _ = refl                     



--========================================================================

module ex3 where

  
  -- Что Миша будет есть?  МСР, 137.

  -- Lex Items
  чтоˡⁱ  = mkLI ("что" ∷ [])  [] (N ∷ [])           []
  Мишаˡⁱ = mkLI ("Миша" ∷ []) [] (N ∷ masc ∷ [])    []
  естьˡⁱ = mkLI ("есть" ∷ []) [] (V ∷ [])           (N ∷ [])
  vˡⁱ    = mkLI ("v" ∷ [])    [] (vᶠ ∷ [])          (V ∷ N ∷ [])
  Tˡⁱ    = mkLI ("T" ∷ [])    [] (Tᶠ ∷ future ∷ []) (vᶠ ∷ N ∷ [])
  Cˡⁱ    = mkLI ("C" ∷ [])    [] (Cᶠ ∷ [])          (Tᶠ ∷ N ∷ [])

  -- Lex Array
  чтоˡᵃ естьˡᵃ Мишаˡᵃ vˡᵃ Tˡᵃ Cˡᵃ : LexArr
  
  чтоˡᵃ  = [ чтоˡⁱ ] 
  естьˡᵃ = естьˡⁱ ∷ чтоˡᵃ
  Мишаˡᵃ = Мишаˡⁱ ∷ vˡᵃ
  vˡᵃ    = vˡⁱ ∷ естьˡᵃ
  Tˡᵃ    = Tˡⁱ ∷ Мишаˡᵃ
  Cˡᵃ    = Cˡⁱ ∷ Tˡᵃ

  -- Syntax Objects
  что  = ⟦ чтоˡᵃ ⟧
  есть = ⟦ естьˡᵃ ⟧
  Миша = ⟦ Мишаˡᵃ ⟧
  v = ⟦ vˡᵃ ⟧
  T = ⟦ Tˡᵃ ⟧
  C = ⟦ Cˡᵃ ⟧

  -- Syntax Tree
  dt = Merge (Select чтоˡᵃ)
             (Merge (Select Cˡᵃ)
                    (Merge (Select Мишаˡᵃ)
                           (Merge (Select Tˡᵃ)
                                  (Merge (Select Мишаˡᵃ)
                                         (Merge (Select vˡᵃ)
                                                (Merge (Select естьˡᵃ)
                                                       (Select чтоˡᵃ)))))))

  -- Syntax Object
  so = DTree→SO dt

  _ : so ≡ ⟦ ("C" ∷ []) ∙ [] ∙ Cᶠ ∷ [] ∙ [] 
             - что 
             - ⟦ ("C" ∷ []) ∙ [] ∙ Cᶠ ∷ [] ∙ N ∷ []  
                 - C 
                 - ⟦ ("T" ∷ []) ∙ [] ∙ Tᶠ ∷ future ∷ [] ∙ [] 
                     - Миша 
                     - ⟦ ("T" ∷ []) ∙ [] ∙ Tᶠ ∷ future ∷ [] ∙ N ∷ [] 
                         - T 
                         - ⟦ ("v" ∷ []) ∙ [] ∙ vᶠ ∷ [] ∙ [] 
                             - Миша 
                             - ⟦ ("v" ∷ []) ∙ [] ∙ vᶠ ∷ [] ∙ N ∷ [] 
                                 - v 
                                 - ⟦ ("есть" ∷ []) ∙ [] ∙ V ∷ [] ∙ [] 
                                     - есть 
                                     - что        ⟧ ⟧ ⟧ ⟧ ⟧ ⟧ ⟧
  _ = refl

  _ : positions so ≡ pos c0 ∷
                     pos (c0 cl) ∷
                     pos (c0 cr) ∷
                     pos (c0 cr cl) ∷
                     pos (c0 cr cr) ∷
                     pos (c0 cr cr cl) ∷
                     pos (c0 cr cr cr) ∷
                     pos (c0 cr cr cr cl) ∷
                     pos (c0 cr cr cr cr) ∷
                     pos (c0 cr cr cr cr cl) ∷
                     pos (c0 cr cr cr cr cr) ∷
                     pos (c0 cr cr cr cr cr cl) ∷
                     pos (c0 cr cr cr cr cr cr) ∷
                     pos (c0 cr cr cr cr cr cr cl) ∷
                     pos (c0 cr cr cr cr cr cr cr) ∷ []
  _ = refl

  _ : nodesNum so ≡ 15
  _ = refl

  _ : edgesNum so ≡ 14
  _ = refl
  
  dt0 = Merge (Select естьˡᵃ) (Select чтоˡᵃ)
  dt1 = Merge (Select vˡᵃ) dt0
  dt2 = Merge (Select Мишаˡᵃ) dt1
  dt3 = Merge (Select Tˡᵃ) dt2
  dt4 = Merge (Select Мишаˡᵃ) dt3
  dt5 = Merge (Select Cˡᵃ) dt4
  dt6 = Merge (Select чтоˡᵃ) dt5
  so0 = DTree→SO dt0
  so1 = DTree→SO dt1
  so2 = DTree→SO dt2
  so3 = DTree→SO dt3
  so4 = DTree→SO dt4
  so5 = DTree→SO dt5
  so6 = DTree→SO dt6

  _ : so ≡ so6
  _ = refl

  _ : positionsSO so ≡ (so ∷ []) ∷
                      (so ∷ что ∷ []) ∷
                      (so ∷ so5 ∷ []) ∷ 
                      (so ∷ so5 ∷ C ∷ []) ∷ 
                      (so ∷ so5 ∷ so4 ∷ []) ∷ 
                      (so ∷ so5 ∷ so4 ∷ Миша ∷ []) ∷ 
                      (so ∷ so5 ∷ so4 ∷ so3 ∷ []) ∷ 
                      (so ∷ so5 ∷ so4 ∷ so3 ∷ T ∷ []) ∷ 
                      (so ∷ so5 ∷ so4 ∷ so3 ∷ so2 ∷ []) ∷ 
                      (so ∷ so5 ∷ so4 ∷ so3 ∷ so2 ∷ Миша ∷ []) ∷ 
                      (so ∷ so5 ∷ so4 ∷ so3 ∷ so2 ∷ so1 ∷ []) ∷ 
                      (so ∷ so5 ∷ so4 ∷ so3 ∷ so2 ∷ so1 ∷ v ∷ []) ∷ 
                      (so ∷ so5 ∷ so4 ∷ so3 ∷ so2 ∷ so1 ∷ so0 ∷ []) ∷ 
                      (so ∷ so5 ∷ so4 ∷ so3 ∷ so2 ∷ so1 ∷ so0 ∷ есть ∷ []) ∷ 
                      (so ∷ so5 ∷ so4 ∷ so3 ∷ so2 ∷ so1 ∷ so0 ∷ что ∷ []) ∷ []
  _ = refl                      

  _ : chainL Миша so ≡ (so ∷ so5 ∷ so4 ∷ Миша ∷ []) ∷
                       (so ∷ so5 ∷ so4 ∷ so3 ∷ so2 ∷ Миша ∷ []) ∷
                       []
  _ = refl

  p1 : path so to Миша
  p1 = c0 cr cr cl

  p2 : path so to Миша
  p2 = c0 cr cr cr cr cl

  _ : sister (pos p1) ≡ just (pos (c0 cr cr cr))
  _ = refl

  _ : sisterL (pos p1) ≡ just so3
  _ = refl

  _ : sisterL (pos p2) ≡ just so1
  _ = refl


  _ : c-commanded (pos p2) ≡ pos (c0 cr cr cr cr cr)
                           ∷ pos (c0 cr cr cr cr cr cl)
                           ∷ pos (c0 cr cr cr cr cr cr)
                           ∷ pos (c0 cr cr cr cr cr cr cl)
                           ∷ pos (c0 cr cr cr cr cr cr cr)
                           ∷ []
  _ = refl

  _ : c-commandedL (pos p2) ≡  
          (so ∷ so5 ∷ so4 ∷ so3 ∷ so2 ∷ so1 ∷ [])
        ∷ (so ∷ so5 ∷ so4 ∷ so3 ∷ so2 ∷ so1 ∷ v ∷ [])
        ∷ (so ∷ so5 ∷ so4 ∷ so3 ∷ so2 ∷ so1 ∷ so0 ∷ [])
        ∷ (so ∷ so5 ∷ so4 ∷ so3 ∷ so2 ∷ so1 ∷ so0 ∷ есть ∷ [])
        ∷ (so ∷ so5 ∷ so4 ∷ so3 ∷ so2 ∷ so1 ∷ so0 ∷ что ∷ [])
        ∷ []
  _ = refl

  _ : c-commandedL {so} (pos (c0 cr cr cr cr cr)) ≡ (so ∷ so5 ∷ so4 ∷ so3 ∷ so2 ∷ Миша ∷ []) ∷ []
  _ = refl
         

  _ : internalMerge? so ≡ true
  _ = refl

  _ : internalMerge? so4 ≡ true
  _ = refl

  _ : internalMerge? so2 ≡ false
  _ = refl


  _ : Constituents so1 ≡ so1 ∷ v ∷ so0 ∷ есть ∷ что ∷ []
  _ = refl

  _ : Constituents so1 ≡ ⟦ ("v" ∷ []) ∙ [] ∙ vᶠ ∷ [] ∙ N ∷ [] 
                           - v 
                           - ⟦ ("есть" ∷ []) ∙ [] ∙ V ∷ [] ∙ [] 
                               - есть 
                               - что ⟧ ⟧
                       ∷ v
                       ∷ ⟦ ("есть" ∷ []) ∙ [] ∙ V ∷ [] ∙ [] 
                           - есть 
                           - что ⟧
                       ∷ есть
                       ∷ что
                       ∷ []
  _ = refl







--========================================================================

module ex1 where

  runᵖ loveᵖ giveᵖ manᵖ toᵖ Johnᵖ Maryᵖ vᵖ : PHONList
  runᵖ  = "run" ∷ []
  loveᵖ = "love" ∷ []
  giveᵖ = "give" ∷ []
  manᵖ  = "man" ∷ []
  toᵖ   = "to" ∷ []
  Johnᵖ = "John" ∷ []
  Maryᵖ = "Mary" ∷ []
  vᵖ    = "v" ∷ []

  -- в uF первое место -- комплемент, второе -- спецификатор
  -- (первый Merge, второй Merge)
  runˡⁱ  = mkLI runᵖ  [] (V ∷ []) (N ∷ [])
  loveˡⁱ = mkLI loveᵖ [] (V ∷ []) (N ∷ N ∷ [])
  giveˡⁱ = mkLI giveᵖ [] (V ∷ []) (N ∷ N ∷ P ∷ [])
  manˡⁱ  = mkLI manᵖ  [] (N ∷ []) []
  toˡⁱ   = mkLI toᵖ   [] (P ∷ []) (N ∷ [])
  Johnˡⁱ = mkLI Johnᵖ [] (N ∷ []) []
  Maryˡⁱ = mkLI Maryᵖ [] (N ∷ []) []
  vˡⁱ    = mkLI vᵖ    [] (vᶠ ∷ []) (V ∷ [])  -- ??

  vˡᵃ : LexArr
  vˡᵃ = [ vˡⁱ ] 
  runˡᵃ : LexArr
  runˡᵃ = runˡⁱ ∷ vˡᵃ
  Johnˡᵃ : LexArr
  Johnˡᵃ = Johnˡⁱ ∷ runˡᵃ
  
  John = ⟦ Johnˡᵃ ⟧
  run  = ⟦ runˡᵃ  ⟧
  v    = ⟦ vˡᵃ    ⟧
  
  s01 = Select runˡᵃ
  s02 = Select Johnˡᵃ
  s1  = Merge s01 s02
  s03 = Select vˡᵃ 
  s2  = Merge s03 s1
  so1  = DTree→SO s1
  so2  = DTree→SO s2
  
  _ : so1 ≡ ⟦ runᵖ ∙ [] ∙ V ∷ [] ∙ [] - run - John ⟧
  _ = refl
  
  _ : so2 ≡ ⟦ vᵖ ∙ [] ∙ vᶠ ∷ [] ∙ [] 
              - v 
              - ⟦ runᵖ ∙ [] ∙ V ∷ [] ∙ [] 
                  - run 
                  - John ⟧ ⟧  
  _ = refl
  

  p2 : so2 contains so2
  p2 = c0

  _ : Path→List p2 ≡ so2 ∷ []
  _ = refl

  p01 : so2 contains run
  p01 = c0 cr cl

  _ : Path→List p01 ≡ so2 ∷ so1 ∷ run ∷ []
  _ = refl


  fastᵖ : PHONList
  fastᵖ = "fast" ∷ []
  fastˡⁱ = mkLI fastᵖ [] (A ∷ []) []
  fastˡᵃ : LexArr
  fastˡᵃ = fastˡⁱ ∷ runˡᵃ
  fast = ⟦ fastˡᵃ ⟧
  
  s04 = Select fastˡᵃ
  s3  = Merge s04 s2
  so3  = DTree→SO s3

  s4 = Merge (Select fastˡᵃ)
             (Merge (Select vˡᵃ)
                    (Merge (Select runˡᵃ)
                           (Select Johnˡᵃ)))
  so4 = DTree→SO s4                               

  _ : s3 ≡ s4
  _ = refl

  _ : so4 ≡ ⟦ vᵖ ∙ [] ∙ vᶠ ∷ [] ∙ [] 
              - fast 
              - ⟦ vᵖ ∙ [] ∙ vᶠ ∷ [] ∙ [] 
                  - v 
                  - ⟦ runᵖ ∙ [] ∙ V ∷ [] ∙ [] 
                      - run 
                      - John ⟧ ⟧ ⟧
  _ = refl
  
  
  Maryˡᵃ : LexArr
  Maryˡᵃ = Maryˡⁱ ∷ runˡᵃ
  Mary = ⟦ Maryˡᵃ ⟧

  run₂ˡᵃ : LexArr
  run₂ˡᵃ = runˡⁱ ∷ Maryˡᵃ
  run₂ = ⟦ run₂ˡᵃ ⟧

  s05 = Select Maryˡᵃ
  
  -- Mary runs
  s5 = Merge s05 (Select run₂ˡᵃ)
  so5 = DTree→SO s5
  
  _ : so5 ≡ ⟦ runᵖ ∙ [] ∙ V ∷ [] ∙ []  
              - Mary 
              - run₂ ⟧
  _ = refl
  
  
  loveˡᵃ : LexArr
  loveˡᵃ = loveˡⁱ ∷ run₂ˡᵃ
  love = ⟦ loveˡᵃ ⟧
  
  -- John loves Mary
  s6 = Merge (Select Johnˡᵃ)
             (Merge (Select loveˡᵃ)
                    (Select Maryˡᵃ))
  so6 = DTree→SO s6                      
  
  _ : so6 ≡ ⟦ loveᵖ ∙ [] ∙ V ∷ [] ∙ [] 
              - John 
              - ⟦ loveᵖ ∙ [] ∙ V ∷ [] ∙ N ∷ [] 
                  - love 
                  - Mary ⟧ ⟧
  _ = refl


  s7 = Merge s6 s05
  s8 = Merge (Select loveˡᵃ) s05
  so7 = DTree→SO s7
  so8 = DTree→SO s8



--   --==  Constituents  ==--
  
  _ : Constituents so1 ≡ ⟦ runᵖ ∙ [] ∙ V ∷ [] ∙ [] - run - John ⟧ ∷
                           run ∷
                           John ∷
                           []
  _ = refl                             
  
  _ : Constituents so2 ≡ ⟦ vᵖ ∙ [] ∙ vᶠ ∷ [] ∙ []
                             - v
                             - ⟦ runᵖ ∙ [] ∙ V ∷ [] ∙ []
                                 - run
                                 - John ⟧ ⟧ ∷  
                           v ∷
                           ⟦ runᵖ ∙ [] ∙ V ∷ [] ∙ []
                             - run
                             - John ⟧ ∷
                           run ∷
                           John ∷
                           []
  _ = refl
  

  _ : so1 contains John 
  _ = c0 cr

  _ : so2 contains so1
  _ = c0 cr

  p7-6 : Position so7
  p7-6 = pos (c0 cl) 

  p7-John : Position so7
  p7-John = pos (c0 cl cl)
  
  p7-love : Position so7
  p7-love = pos (c0 cl cr cl)

  p7-Mary1 : Position so7
  p7-Mary1 = pos (c0 cr)

  p7-Mary2 : Position so7
  p7-Mary2 = pos (c0 cl cr cr)


  --==   Internal Merge  ==--

  _ : internalMerge? so1 ≡ false
  _ = refl

  _ : internalMerge? so2 ≡ false
  _ = refl

  _ : internalMerge? so3 ≡ false   -- Adjoin
  _ = refl

  _ : internalMerge? so5 ≡ false
  _ = refl

  _ : Constituents so6 ≡ so6 ∷ John ∷ so8 ∷ ⟦ loveˡᵃ ⟧ ∷ Mary ∷ []   
  _ = refl

  _ : Constituents so8 ≡ so8 ∷ ⟦ loveˡᵃ ⟧ ∷ Mary ∷ []   
  _ = refl

  _ : so6 containsᵇ John ≡ true
  _ = refl
  
  _ : internalMerge? so6 ≡ false
  _ = refl

  _ : Constituents so7 ≡ so7 ∷ so6 ∷ Mary ∷ John ∷ so8 ∷ ⟦ loveˡᵃ ⟧ ∷ Mary ∷ []   
  _ = refl

  _ : internalMerge? so7 ≡ true
  _ = refl



  -- c-command

  _ : c-commanded p7-6 ≡ pos (c0 cr) ∷ []
  _ = refl

  _ : c-commanded p7-John ≡ pos (c0 cl cr)
                          ∷ pos (c0 cl cr cl)
                          ∷ pos (c0 cl cr cr)
                          ∷ []
  _ = refl

  _ : c-commanded p7-Mary1 ≡ pos (c0 cl) 
                           ∷ pos (c0 cl cl) 
                           ∷ pos (c0 cl cr)
                           ∷ pos (c0 cl cr cl)
                           ∷ pos (c0 cl cr cr)
                           ∷ [] 
  _ = refl

  _ : c-commanded p7-Mary2 ≡ pos (c0 cl cr cl) ∷ []
  _ = refl

  _ : c-commanded p7-love ≡ pos (c0 cl cr cr) ∷ []
  _ = refl

