module _ where

open import Data.Bool using (Bool; true; false)
open import Data.Fin
open import Data.Maybe
open import Data.Nat
open import Data.List hiding ([_])
open import Relation.Binary.PropositionalEquality hiding ([_])

open import SyntaxObject


module ex5 where
  
  -- В пятницу Маша ела кашу.
  
  в-пятницу/li = mkLI (P ∷ decl ∷ []) []
  Маша/li      = mkLI (N ∷ fem ∷ [])     []
  ела/li       = mkLI (V ∷ past ∷ [])            (N ∷ [])
  кашу/li      = mkLI (N ∷ fem ∷ ACC ∷ [])     []
  v/fc = mkFC (vᶠ ∷ [])        (V ∷ N ∷ [])
  T/fc = mkFC (Tᶠ ∷ past ∷ []) (vᶠ ∷ N ∷ P ∷ [])
  C/fc = mkFC (Cᶠ ∷ [])        (Tᶠ ∷ N ∷ Wh:* ∷ [])
  
  в-пятницу/e = lex в-пятницу/li ⊣
  
  ела/e : Enum _
  ела/e = lex ела/li ∷ в-пятницу/e
  
  v/e : Enum _
  v/e = fun v/fc ∷ ела/e
  
  Маша/e : Enum _
  Маша/e = lex Маша/li ∷ v/e
  
  кашу/e : Enum _
  кашу/e = lex кашу/li ∷ Маша/e
  
  T/e : Enum _
  T/e = fun T/fc ∷ кашу/e
  
  C/e : Enum _
  C/e = fun C/fc ∷ T/e
  
  в-пятницу = ⟦ в-пятницу/e ⊣⟧
  Маша      = ⟦ Маша/e ⊣⟧
  ела       = ⟦ ела/e ⊣⟧
  кашу      = ⟦ кашу/e ⊣⟧
  𝑣 = ⟦ v/e ⊣⟧
  T = ⟦ T/e ⊣⟧
  C = ⟦ C/e ⊣⟧
  
  st = Merge (# 0) (# 1) &
       Select C/e &
       Merge (# 0) (# 1) &
       Select в-пятницу/e &
       Merge (# 0) (# 1) &
       Select Маша/e &
       Merge (# 0) (# 1) &
       Select T/e &
       Merge (# 0) (# 1) &
       Select v/e &
       Merge (# 0) (# 1) &
       Select ела/e &
       Select кашу/e &
       ∅
  
  
  _ : st [ # 12 ] ≡ кашу
  _ = refl
  
  _ : st [ # 10 ] ≡ ⟦ V ∷ past ∷ [] ∙ [] -
                       ела -
                       кашу
                    ⟧ 
  _ = refl
  
  _ : st [ # 8 ] ≡ ⟦ vᶠ ∷ [] ∙ N ∷ [] -
                       𝑣 -
                       ⟦ V ∷ past ∷ [] ∙ []  -
                           ела -
                           кашу
                       ⟧
                   ⟧ 
  _ = refl
  
  -- _ : st [ # 7 ] ≡ ⟦ vᶠ ∷ [] ∙ []  -
  --                      ты -
  --                      ⟦ vᶠ ∷ [] ∙ N ∷ []  -
  --                          𝑣 -
  --                          ⟦  V ∷ [] ∙ []  -
  --                              купил -
  --                              какую-машину
  --                          ⟧
  --                      ⟧
  --                  ⟧ 
  -- _ = refl
  
  -- _ : st [ # 3 ] ≡ ⟦ Tᶠ ∷ past ∷ [] ∙ N ∷ []  -
  --                      T -
  --                      ⟦ vᶠ ∷ [] ∙ []  -
  --                          ты -
  --                          ⟦ vᶠ ∷ [] ∙ N ∷ []  -
  --                              𝑣 -
  --                              ⟦ V ∷ [] ∙ []  -
  --                                  купил -
  --                                  какую-машину
  --                              ⟧
  --                          ⟧
  --                      ⟧
  --                 ⟧
  -- _ = refl
  
  -- _ : st [ # 2 ] ≡ ⟦ Tᶠ ∷ past ∷ [] ∙ [] -
  --                      ты -
  --                      st [ # 3 ]
  --                  ⟧ 
  -- _ = refl
  
  -- _ : st [ # 0 ] ≡ ⟦ Cᶠ ∷ [] ∙ N ∷ []  -
  --                      C -
  --                      st [ # 2 ]
  --                  ⟧ 
  -- _ = refl
  
  -- _ : st [ # 0 ] ≡ ⟦ Cᶠ ∷ [] ∙ [] -
  --                      что -
  --                      ⟦ Cᶠ ∷ [] ∙ N ∷ []  -
  --                          C -
  --                          ⟦ Tᶠ ∷ future ∷ [] ∙ [] -
  --                              Миша -
  --                              ⟦ Tᶠ ∷ future ∷ [] ∙ N ∷ [] -
  --                                  T -
  --                                  ⟦ vᶠ ∷ [] ∙ [] -
  --                                      Миша -
  --                                      ⟦ vᶠ ∷ [] ∙ N ∷ [] -
  --                                          𝑣 -
  --                                          ⟦ V ∷ [] ∙ [] -
  --                                              есть -
  --                                              что        ⟧ ⟧ ⟧ ⟧ ⟧ ⟧ ⟧
  -- _ = refl
  
  


--========================================================================

module ex4 where

  -- Какую машину ты купил?  МСР, 146 и сл..
  
  какую-машину/li  = mkLI (N ∷ question ∷ []) []
  ты/li            = mkLI (N ∷ masc ∷ [])     []
  купил/li         = mkLI (V ∷ [])            (N ∷ [])
  v/fc = mkFC (vᶠ ∷ [])        (V ∷ N ∷ [])
  T/fc = mkFC (Tᶠ ∷ past ∷ []) (vᶠ ∷ N ∷ [])
  C/fc = mkFC (Cᶠ ∷ [])        (Tᶠ ∷ N ∷ Wh:* ∷ [])
  
  какую-машину/e = lex какую-машину/li ⊣
  
  купил/e : Enum _
  купил/e = lex купил/li ∷ какую-машину/e
  
  v/e : Enum _
  v/e = fun v/fc ∷ купил/e
  
  ты/e : Enum _
  ты/e = lex ты/li ∷ v/e
  
  T/e : Enum _
  T/e = fun T/fc ∷ ты/e
  
  C/e : Enum _
  C/e = fun C/fc ∷ T/e
  
  какую-машину  = ⟦ какую-машину/e ⊣⟧
  купил         = ⟦ купил/e ⊣⟧
  ты            = ⟦ ты/e ⊣⟧
  𝑣 = ⟦ v/e ⊣⟧
  T = ⟦ T/e ⊣⟧
  C = ⟦ C/e ⊣⟧
  
  st = Merge (# 0) (# 1) &
       Select C/e &
       Merge (# 3) (# 0) &
       Merge (# 0) (# 1) &
       Select T/e &
       Merge (# 0) (# 1) &
       Select ты/e &
       Merge (# 0) (# 1) &
       Select v/e &
       Merge (# 0) (# 1) &
       Select купил/e &
       Select какую-машину/e &
       ∅
  
  
  _ : st [ # 11 ] ≡ какую-машину 
  _ = refl
  
  _ : st [ # 9 ] ≡ ⟦ V ∷ [] ∙ [] -
                       купил -
                       какую-машину
                   ⟧ 
  _ = refl
  
  _ : st [ # 7 ] ≡ ⟦ vᶠ ∷ [] ∙ N ∷ [] -
                       𝑣 -
                       ⟦ V ∷ [] ∙ []  -
                           купил -
                           какую-машину
                       ⟧
                   ⟧ 
  _ = refl
  
  _ : st [ # 5 ] ≡ ⟦ vᶠ ∷ [] ∙ []  -
                       ты -
                       ⟦ vᶠ ∷ [] ∙ N ∷ []  -
                           𝑣 -
                           ⟦  V ∷ [] ∙ []  -
                               купил -
                               какую-машину
                           ⟧
                       ⟧
                   ⟧ 
  _ = refl
  
  _ : st [ # 3 ] ≡ ⟦ Tᶠ ∷ past ∷ [] ∙ N ∷ []  -
                       T -
                       ⟦ vᶠ ∷ [] ∙ []  -
                           ты -
                           ⟦ vᶠ ∷ [] ∙ N ∷ []  -
                               𝑣 -
                               ⟦ V ∷ [] ∙ []  -
                                   купил -
                                   какую-машину
                               ⟧
                           ⟧
                       ⟧
                  ⟧
  _ = refl
  
  _ : st [ # 2 ] ≡ ⟦ Tᶠ ∷ past ∷ [] ∙ [] -
                       ты -
                       st [ # 3 ]
                   ⟧ 
  _ = refl
  
  -- _ : st [ # 0 ] ≡ ⟦ Cᶠ ∷ [] ∙ N ∷ []  -
  --                      C -
  --                      st [ # 2 ]
  --                  ⟧ 
  -- _ = refl
  
  -- _ : st [ # 0 ] ≡ ⟦ Cᶠ ∷ [] ∙ [] -
  --                      что -
  --                      ⟦ Cᶠ ∷ [] ∙ N ∷ []  -
  --                          C -
  --                          ⟦ Tᶠ ∷ future ∷ [] ∙ [] -
  --                              Миша -
  --                              ⟦ Tᶠ ∷ future ∷ [] ∙ N ∷ [] -
  --                                  T -
  --                                  ⟦ vᶠ ∷ [] ∙ [] -
  --                                      Миша -
  --                                      ⟦ vᶠ ∷ [] ∙ N ∷ [] -
  --                                          𝑣 -
  --                                          ⟦ V ∷ [] ∙ [] -
  --                                              есть -
  --                                              что        ⟧ ⟧ ⟧ ⟧ ⟧ ⟧ ⟧
  -- _ = refl
  
  

--========================================================================

module ex3 where

  
  -- Что Миша будет есть?  МСР, 137.
  
  что/li  = mkLI (N ∷ [])        []
  Миша/li = mkLI (N ∷ masc ∷ []) []
  есть/li = mkLI (V ∷ [])        (N ∷ [])
  v/fc = mkFC (vᶠ ∷ [])          (V ∷ N ∷ [])
  T/fc = mkFC (Tᶠ ∷ future ∷ []) (vᶠ ∷ N ∷ [])
  C/fc = mkFC (Cᶠ ∷ [])          (Tᶠ ∷ N ∷ [])
  
  что/e = lex что/li ⊣
  
  есть/e : Enum _
  есть/e = lex есть/li ∷ что/e
  
  v/e : Enum _
  v/e = fun v/fc ∷ есть/e
  
  Миша/e : Enum _
  Миша/e = lex Миша/li ∷ v/e
  
  T/e : Enum _
  T/e = fun T/fc ∷ Миша/e
  
  C/e : Enum _
  C/e = fun C/fc ∷ T/e
  
  что  = ⟦ что/e ⊣⟧
  есть = ⟦ есть/e ⊣⟧
  Миша = ⟦ Миша/e ⊣⟧
  𝑣 = ⟦ v/e ⊣⟧
  T = ⟦ T/e ⊣⟧
  C = ⟦ C/e ⊣⟧
  
  st = Merge (# 11) (# 0) &
       Merge (# 0) (# 1) &
       Select C/e &
       Merge (# 3) (# 0) &
       Merge (# 0) (# 1) &
       Select T/e &
       Merge (# 0) (# 1) &
       Select Миша/e &
       Merge (# 0) (# 1) &
       Select v/e &
       Merge (# 0) (# 1) &
       Select есть/e &
       Select что/e &
       ∅
  
  
  _ : st [ # 12 ] ≡ что 
  _ = refl
  
  _ : st [ # 10 ] ≡ ⟦ V ∷ [] ∙ [] -
                       есть -
                       что
                   ⟧ 
  _ = refl
  
  _ : st [ # 8 ] ≡ ⟦ vᶠ ∷ [] ∙ N ∷ [] -
                       𝑣 -
                       ⟦ V ∷ [] ∙ []  -
                           есть -
                           что
                       ⟧
                   ⟧ 
  _ = refl
  
  _ : st [ # 6 ] ≡ ⟦ vᶠ ∷ [] ∙ []  -
                       Миша -
                       ⟦ vᶠ ∷ [] ∙ N ∷ []  -
                           𝑣 -
                           ⟦  V ∷ [] ∙ []  -
                               есть -
                               что
                           ⟧
                       ⟧
                   ⟧ 
  _ = refl
  
  _ : st [ # 4 ] ≡ ⟦ Tᶠ ∷ future ∷ [] ∙ N ∷ []  -
                       T -
                       ⟦ vᶠ ∷ [] ∙ []  -
                           Миша -
                           ⟦ vᶠ ∷ [] ∙ N ∷ []  -
                               𝑣 -
                               ⟦ V ∷ [] ∙ []  -
                                   есть -
                                   что
                               ⟧
                           ⟧
                       ⟧
                  ⟧
  _ = refl
  
  _ : st [ # 3 ] ≡ ⟦ Tᶠ ∷ future ∷ [] ∙ [] -
                       Миша -
                       st [ # 4 ]
                   ⟧ 
  _ = refl
  
  _ : st [ # 1 ] ≡ ⟦ Cᶠ ∷ [] ∙ N ∷ []  -
                       C -
                       st [ # 3 ]
                   ⟧ 
  _ = refl
  
  _ : st [ # 0 ] ≡ ⟦ Cᶠ ∷ [] ∙ [] -
                       что -
                       ⟦ Cᶠ ∷ [] ∙ N ∷ []  -
                           C -
                           ⟦ Tᶠ ∷ future ∷ [] ∙ [] -
                               Миша -
                               ⟦ Tᶠ ∷ future ∷ [] ∙ N ∷ [] -
                                   T -
                                   ⟦ vᶠ ∷ [] ∙ [] -
                                       Миша -
                                       ⟦ vᶠ ∷ [] ∙ N ∷ [] -
                                           𝑣 -
                                           ⟦ V ∷ [] ∙ [] -
                                               есть -
                                               что        ⟧ ⟧ ⟧ ⟧ ⟧ ⟧ ⟧
  _ = refl
  
  
  
module ex2 where

  -- согласование
  
  страус/li  = mkLI (N ∷ masc ∷ singular ∷ []) (Number: ∷ [])
  страусы/li = mkLI (N ∷ masc ∷ plural ∷ []) []
  -- спать/li    = mkLI (V ∷ []) (N ∷ Number: ∷ [])
  спит/li    = mkLI (V ∷ singular ∷ []) (N ∷ [])
  спят/li    = mkLI (V ∷ plural ∷ []) (N ∷ [])
  
  страус/e = lex страус/li ⊣
  страусы/e : Enum _
  страусы/e = lex страусы/li ∷ страус/e
  -- спать/e : Enum _
  -- спать/e  = lex спать/li ∷ страусы/e
  спит/e : Enum _
  спит/e  = lex спит/li ∷ страусы/e
  спят/e : Enum _
  спят/e  = lex спят/li ∷ страусы/e


  -- страус спит
  
  st1 = Merge (# 0) (# 1) &
        Select спит/e &
        Select страус/e &
        ∅
  
  -- страусы спят
  
  st2 = Merge (# 0) (# 1) &
        Select спят/e &
        Select страусы/e &
        ∅
  
  -- некорректные деревья  ???
  
  st3 = Merge (# 0) (# 1) &
        Select спят/e &
        Select страус/e &
        ∅
  
  st4 = Merge (# 0) (# 1) &
        Select спит/e &
        Select страусы/e &
        ∅
  


--========================================================================

module ex1 where

  -- в uF первое место -- комплимент, второе -- спецификатор
  run/li  = mkLI (V ∷ []) (N ∷ [])
  love/li = mkLI (V ∷ []) (N ∷ N ∷ [])
  give/li = mkLI (V ∷ []) (N ∷ N ∷ P ∷ [])
  man/li  = mkLI (N ∷ []) []
  to/li   = mkLI (P ∷ []) (N ∷ [])
  John/li = mkLI (N ∷ []) []
  Mary/li = mkLI (N ∷ []) []
  
  v/fc = mkFC (vᶠ ∷ []) (V ∷ [])  -- ??

  v/e : Enum 1
  v/e = fun v/fc ⊣
  run/e : Enum 2
  run/e = lex run/li ∷ v/e
  John/e : Enum 3
  John/e = lex John/li ∷ run/e
  
  John = ⟦ John/e ⊣⟧
  run  = ⟦ run/e  ⊣⟧
  v    = ⟦ v/e    ⊣⟧
  
  st0 = Select run/e & Select John/e & ∅ 
  st1 = Merge (# 0) (# 1) & st0
  st2 = Merge (# 0) (# 1) & Select v/e & st1  
  
  _ : st2 ≡ Merge (# 0) (# 1) &
            Select v/e &
            Merge (# 0) (# 1) &
            Select run/e &
            Select John/e &
            ∅
  _ = refl
  
  
  _ : st0 [ # 0 ] ≡ run
  _ = refl
  
  _ : st0 [ # 1 ] ≡ John
  _ = refl
  
  _ : st1 [ # 0 ] ≡ ⟦ V ∷ [] ∙ [] - run - John ⟧
  _ = refl
  
  _ : st1 [ # 1 ] ≡ run 
  _ = refl
  
  _ : st2 [ # 0 ] ≡ ⟦ vᶠ ∷ [] ∙ [] 
                      - v 
                      - ⟦ V ∷ [] ∙ [] 
                          - run 
                          - John ⟧ ⟧  
  _ = refl
  
  _ : st2 [ # 1 ] ≡ v
  _ = refl
  
  _ : st2 [ # 2 ] ≡ ⟦ V ∷ [] ∙ [] - run - John ⟧
  _ = refl
  
  _ : st2 [ # 3 ] ≡ run 
  _ = refl
  
  fast/li = mkLI (Adj ∷ []) []
  fast/e : Enum _
  fast/e = lex fast/li ∷ run/e
  fast = ⟦ fast/e ⊣⟧
  
  st3 = Adjoin (# 0) (# 1) &
        Select fast/e &
        st2
  
  st4 = Adjoin (# 0) (# 1) &
        Select fast/e &
        Merge (# 0) (# 1) &
        Select v/e &
        Merge (# 0) (# 1) &
        Select run/e &
        Select John/e &
        ∅
  
  _ : st3 ≡ st4
  _ = refl
  
  
  
  -- ⋘_∙_⋙ : FList → FList → Maybe Label
  -- ⋘ ⋙ ⋐ ⋑ ‿ ⋯ —  ⌟⌞ ~~ ╴╵╶╷ ⋆ ◂▸ ◃▹ 
  -- 【_-_-_】  ⁅ ⁆ [[_-_-_]]
  
  
  _ : st4 [ # 0 ] ≡ ⟦ vᶠ ∷ [] ∙ [] -
                        fast -
                        ⟦ vᶠ ∷ [] ∙ [] -
                            v -
                            ⟦ V ∷ [] ∙ [] -
                                run -
                                John
                            ⟧
                        ⟧
                     ⟧
  _ = refl
  
  
  Mary/e : Enum _
  Mary/e = lex Mary/li ∷ run/e
  Mary = ⟦ Mary/e ⊣⟧

  run₂/e : Enum _
  run₂/e = lex run/li ∷ Mary/e
  run₂ = ⟦ run₂/e ⊣⟧
  
  -- Mary runs
  st5 = Merge (# 1) (# 0) &
        Select run₂/e &
        Select Mary/e &
        st2
  
  
  _ : st5 [ # 0 ] ≡ ⟦ V ∷ [] ∙ []  -
                      Mary -
                      run₂ ⟧
  _ = refl
  
  
  love/e : Enum _
  love/e = lex love/li ∷ run₂/e
  love = ⟦ love/e ⊣⟧
  
  -- John loves Mary
  st6 = Merge (# 9) (# 0) &
        Merge (# 0) (# 3) &
        Select love/e &
        st5 
  
  _ : st6 [ # 10 ] ≡ John
  _ = refl
  
  
  _ : st6 [ # 0 ] ≡ ⟦ V ∷ [] ∙ [] -
                      John -
                      ⟦ V ∷ [] ∙ N ∷ [] -
                        love -
                        Mary ⟧ ⟧
  _ = refl
  
  
  st7 = Adjoin (# 0) (# 1) &
        Select John/e &
        Select fast/e &
        ∅



  --==  Constituents  ==--
  
  _ : Constituents st1 (# 0) ≡ ⟦ V ∷ [] ∙ [] - run - John ⟧ ∷
                               run ∷
                               John ∷
                               []
  _ = refl                             
  
  _ : Constituents st2 (# 0) ≡ ⟦ vᶠ ∷ [] ∙ []
                                 - v
                                 - ⟦ V ∷ [] ∙ []
                                     - run
                                     - John ⟧ ⟧ ∷  
                               v ∷
                               ⟦ V ∷ [] ∙ [] - run - John ⟧ ∷
                               run ∷
                               John ∷
                               []
  _ = refl
  
  _ : Constituents st2 (# 1) ≡ v ∷ []
  _ = refl
  
  _ : Constituents st2 (# 2) ≡ ⟦ V ∷ [] ∙ [] - run - John ⟧ ∷
                               run ∷
                               John ∷
                               []
  _ = refl
  


  --==   Path  ==--

  
  _ : path-exists? st0 (# 0) ≡ true
  _ = refl
  
  _ : path-exists? st0 (# 1) ≡ false
  _ = refl
  
  _ : path-exists? st1 (# 0) ≡ true
  _ = refl
  
  _ : path-exists? st1 (# 1) ≡ true
  _ = refl
  
  _ : path-exists? st1 (# 2) ≡ true
  _ = refl
  
  _ : path-exists? st2 (# 0) ≡ true
  _ = refl
  
  _ : path-exists? st2 (# 1) ≡ true
  _ = refl
  
  _ : path-exists? st2 (# 2) ≡ true
  _ = refl
  
  _ : path-exists? st2 (# 3) ≡ true
  _ = refl
  
  _ : path-exists? st2 (# 4) ≡ true
  _ = refl
  
  _ : path-exists? (rest st2 (# 1)) (# 0) ≡ true
  _ = refl
  
  _ : path-exists? (rest st2 (# 1)) (# 1) ≡ false
  _ = refl
  
  _ : path-exists? (rest st2 (# 1)) (# 2) ≡ false
  _ = refl
  
  _ : path-exists? (rest st2 (# 2)) (# 0) ≡ true
  _ = refl
  
  _ : path-exists? (rest st2 (# 2)) (# 1) ≡ true
  _ = refl
  
  _ : path-exists? (rest st2 (# 2)) (# 2) ≡ true
  _ = refl
  
  
