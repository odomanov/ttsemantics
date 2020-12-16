module _ where

open import Data.Bool 
open import Data.Integer hiding (_*_)
open import Data.Nat as ℕ using (suc; ℕ; _∸_; _⊔_)
open import Data.String as S using (String) renaming (_++_ to _+++_)

-- float arithmetics

open import Data.Float public using (Float; fromℕ) 
  renaming ( _≤ᵇ_ to infix  5 _[<]_
           ; _+_  to infixl 6 _[+]_
           ; _-_  to infixl 6 _[-]_
           ; _≡ᵇ_ to infix  5 _[=]_
           ; _*_  to infixl 7 _[*]_
           ; _÷_  to infixl 7 _[/]_
           )

infix 5 _[≤]_

_[≤]_ : Float → Float → Bool 
x [≤] y = (x Data.Float.≤ᵇ y) ∨ (x [=] y) 


-- Some Docs

open import WLPretty public

docFloat : Float → Doc
docFloat x = text (Data.Float.show x)

-- rounded to n decimal places
docFloatRounded : ℕ → Float → Doc
docFloatRounded n x = text (Data.Float.show ((Data.Float.round (x [*] 10^n)) /10^n))
  where
  10^n = tofloat (Data.Float.round (Data.Float.e^ ((fromℕ n) [*] (Data.Float.log 10.0))))
    where
    tofloat : ℤ → Float
    tofloat (+ n) = (fromℕ n) [*] 1.0
    tofloat (-[1+ n ]) = (fromℕ (n ∸ 1)) [*] 1.0
  
  _/10^n : ℤ → Float
  (+ n) /10^n = (fromℕ n) [/] 10^n
  (-[1+ n ]) /10^n = Data.Float.-_ ((fromℕ (n ∸ 1)) [/] 10^n)


