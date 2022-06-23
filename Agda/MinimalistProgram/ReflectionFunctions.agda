-- Utility functions fr working with Reflection

module _ where

open import Data.Bool
open import Data.List as 𝕃
open import Data.Maybe

open import Agda.Builtin.Reflection 
open import Reflection public

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
map2 f (x ∷ xs) l = 𝕃.map (f x) l ++ map2 f xs l 

map2Maybe : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
            → (A → B → Maybe C) → List A → List B → List C
map2Maybe f [] _ = []
map2Maybe f _ [] = []
map2Maybe f (x ∷ xs) l = 𝕃.mapMaybe (f x) l ++ map2Maybe f xs l 

mk-cls : Name → Name → Clause
mk-cls q1 q2 with primQNameEquality q1 q2
... | true  = clause [] (vra (con q1 []) ∷ vra (con q2 []) ∷ []) (con (quote true)  [])
... | false = clause [] (vra (con q1 []) ∷ vra (con q2 []) ∷ []) (con (quote false) [])

