module Examples.ExBlackHoles where

open import Data.Empty
open import Data.String as S renaming (_++_ to _+++_)
open import Relation.Binary.PropositionalEquality

open import PersuasionAlgebras.Standard
open import ResiduatedLattices.Standard hiding (⊥)


-- pa = Łuk
-- pa = Gödel
-- pa = Product
pa = ProductRL
-- pa = persuasionAlgebra ProductRL

open import FuzzyTT pa {{RLtoPA}}

postulate 
  I-хорошо-известно : Set
  I-в-центре-практически-каждой-крупной-галактики-находится-массивная-чёрная-дыра : Set
  I-самые-тяжёлые-галактики-окружены-самыми-массивными-гало-из-тёмной-материи : Set
  I-тёмная-материя-играет-ключевую-роль-в-росте-чёрных-дыр : Set
  I-учёные-из-Института-внеземной-физики : Set
  I-исследования-учёных-показали-что-связи-не-существует : Set
  I-исследования-учёных-показали-что-рост-определяется : Set
  I-такой-прямой-связи-не-существует : Set
  I-рост-чёрной-дыры-определяется-процессом-формирования-галактического-ядра : Set

S1 = I-хорошо-известно
S2 = I-в-центре-практически-каждой-крупной-галактики-находится-массивная-чёрная-дыра
S3 = I-самые-тяжёлые-галактики-окружены-самыми-массивными-гало-из-тёмной-материи
S4 = I-тёмная-материя-играет-ключевую-роль-в-росте-чёрных-дыр
S5 = I-учёные-из-Института-внеземной-физики
S6 = I-исследования-учёных-показали-что-связи-не-существует
S7 = I-исследования-учёных-показали-что-рост-определяется
S8 = I-такой-прямой-связи-не-существует
S9 = I-рост-чёрной-дыры-определяется-процессом-формирования-галактического-ядра
A1 = S1 → Fuzzy S2
A2 = S2 → S3 → Fuzzy S4
A4 = S7 → S5 → Fuzzy S9
S4-9 = S4 → Fuzzy (S9 → ⊥)
S9-4 = S9 → Fuzzy (S4 → ⊥)

postulate
  s1 : S1 
  s2 : S2 
  s3 : S3 
  s4 : S4 
  s5 : S5 
  s6 : S6 
  s7 : S7 
  s8 : S8 
  s9 : S9 

fs1 : Fuzzy S1
fs1 = s1 ! mkFUnit 0.9 refl refl

fs3 : Fuzzy S3
fs3 = s3 ! mkFUnit 0.9 refl refl

fs5 : Fuzzy S5
fs5 = s5 ! mkFUnit 0.8 refl refl

fs7 : Fuzzy S7
fs7 = s7 ! mkFUnit 0.8 refl refl

postulate
  a1   : S1 → S2
  a2   : S2 → S3 → S4
  a4   : S7 → S5 → S9
  s4-9 : S4 → S9 → ⊥
  s9-4 : S9 → S4 → ⊥

fa1 : A1
fa1 a = a1 a ! mkFUnit 0.7 refl refl

fa2 : A2
fa2 a b = a2 a b ! mkFUnit 0.8 refl refl

fa4 : A4
fa4 x y = a4 x y ! mkFUnit 1.0 refl refl

fs4-9 : S4-9
fs4-9 x = s4-9 x ! mkFUnit 1.0 refl refl

fs9-4 : S9-4
fs9-4 x = s9-4 x ! mkFUnit 1.0 refl refl


fs2 = fs1 >>= fa1

fs4 = join (fa2 <$> fs2 <*> fs3)

f¬s9 = fs4-9 =<< fs4

fs9 = join (fa4 <$> fs7 <*> fs5)

f¬s4 = fs9-4 =<< fs9

f⊥4 = f¬s4 <*> fs4
f⊥9 = f¬s9 <*> fs9






------------------------------------------------------------------------

open import WLPretty

open import IO

ws = 80 


main = run (putStrLn stringToPrint)
  where
  stringToPrint = ""
    +++   "S1   = " +++ ppretty ws (doc pa (fα fs1))
    +++ "\nS2   = " +++ ppretty ws (doc pa (fα fs2))
    +++ "\nS3   = " +++ ppretty ws (doc pa (fα fs3))
    +++ "\nS4   = " +++ ppretty ws (doc pa (fα fs4))
    +++ "\nS5   = " +++ ppretty ws (doc pa (fα fs5))
    +++ "\nS7   = " +++ ppretty ws (doc pa (fα fs7))
    +++ "\nS9   = " +++ ppretty ws (doc pa (fα fs9))
    +++ "\nA1   = " +++ ppretty ws (doc pa (fα (fa1 s1)))
    +++ "\nA2   = " +++ ppretty ws (doc pa (fα (fa2 s2 s3)))
    +++ "\nA4   = " +++ ppretty ws (doc pa (fα (fa4 s7 s5)))
    +++ "\nS4-9 = " +++ ppretty ws (doc pa (fα (fs4-9 s4)))
    +++ "\nS9-4 = " +++ ppretty ws (doc pa (fα (fs9-4 s9)))
    +++ "\n-S4  = " +++ ppretty ws (doc pa (fα (f¬s4)))
    +++ "\n-S9  = " +++ ppretty ws (doc pa (fα (f¬s9)))
    +++ "\nbot4 = " +++ ppretty ws (doc pa (fα (f⊥4)))
    +++ "\nbot9 = " +++ ppretty ws (doc pa (fα (f⊥9)))
