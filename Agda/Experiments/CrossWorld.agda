-- Cross-World Predication

open import Data.Product

module CrossWorld where

postulate
  World : Set
  _≈>_ : World → World → Set  -- w1 ≈> w2    "w2 достижим из w1"
  w0 : World                  -- актуальный мир

-- Достижимые миры.
acc : World → Set
acc w = Σ[ x ∈ World ] w ≈> x
  -- where
  -- P : World → Set
  -- P w1 = w ≈> w1

-- Возможно в мире w
◇ : World → (P : World → Set) → Set
◇ w P = Σ[ x ∈ (acc w) ] P (proj₁ x)

-- Необходимо в мире w
□ : World → (P : World → Set) → Set
□ w P = ∀ (x : acc w) → P (proj₁ x)



-- ===========================================
-- I could have been taller than I actually am.
-- Я мог бы быть выше, чем я есть.

module I1 where

  postulate
    I : Set           -- возможный я
    ^I : World → I    -- интенсионал I
    taller : I → I → Set
  
  -- Я в мире w1 выше меня в мире w2
  data ^taller : World → World → Set where
    i : ∀ {w1 w2} → taller (^I w1) (^I w2) → ^taller w1 w2
  
  -- Предикат: Я в мире w выше меня в актуальном мире
  taller0 = λ w → ^taller w w0
  
  -- I could have been taller than I actually am.
  -- Я мог бы быть выше, чем я есть.
  trm = ◇ w0 taller0
  
  -- то же в явной форме:
  trm2 = Σ[ w ∈ acc w0 ] taller (^I (proj₁ w)) (^I w0)


-- Другой вариант

module I2 where

  postulate
    D  : World → Set                -- домены
    ^I : (w : World) → D w          -- интенсионал "Я"
    taller : ∀ {w1 w2} → D w1 → D w2 → Set 

  -- Я в мире w1 выше меня в мире w2
  data ^taller : World → World → Set where
    i : ∀ {w1 w2} → taller (^I w1) (^I w2) → ^taller w1 w2
  
  -- Дальше всё аналогично

  -- Предикат: Я в мире w выше меня в актуальном мире
  taller0 = λ w → ^taller w w0
  
  -- I could have been taller than I actually am.
  -- Я мог бы быть выше, чем я есть.
  trm = ◇ w0 taller0
  
  -- то же в явной форме:
  trm2 = Σ[ w ∈ acc w0 ] taller (^I (proj₁ w)) (^I w0)

  


-- Джон мог бы быть богаче

module I3 where
  postulate
    D : World → Set
    ^J : (w : World) → D w                  -- Джон в мире w
    richer : ∀ {w1 w2} → D w1 → D w2 → Set  -- чел в мире w1 богаче чела в мире w2

  -- Джон в мире w1 богаче Джона в мире w2
  data Jr : World → World → Set where
    i : ∀ {w1 w2} → richer (^J w1) (^J w2) → Jr w1 w2

  -- Джон в мире w богаче Джона в актуальном мире
  Jr0 = λ w → Jr w w0

  -- Джон мог бы быть богаче
  p1 = ◇ w0 Jr0
  p2 = ∀ (w : acc w0) → richer (^J (proj₁ w)) (^J w0)


  

-- =======================================================
-- Everyone could have been smarter than they actually are.
-- Каждый мог бы быть умнее, чем есть.

-- УПРАЖНЕНИЕ


-- =========================================================
-- A polar bear could be bigger than a grizzly bear could be.
-- Полярные медведи могли бы быть больше, чем могли бы быть гризли.
-- (некий) полярный медведь мог бы быть больше, чем мог бы быть (некий) гризли.

-- УПРАЖНЕНИЕ



-- Джон богаче, чем когда-либо прежде
-- Джон был богаче, чем когда-либо прежде

postulate
  Time : Set                 -- моменты времени
  _<_  : Time → Time → Set   -- t1 предшествует t2
  t0   : Time                -- момент "сейчас"
  J    : Set                 -- Джон в разные моменты
  ^J   : Time → J
  _is-richer-than_ : J → J → Set

-- предшествующие моменты
before : Time → Set
before t = Σ Time (λ x → x < t)




-- Джон богаче, чем когда-либо прежде
jr0 = ∀ (t : before t0) → (^J t0) is-richer-than (^J (proj₁ t)) 


-- Джон был богаче, чем когда-либо прежде
postulate
  tp    : Time        -- момент в прошлом
  tp<t0 : tp < t0
  
jr = ∀ (t : before tp) → (^J tp) is-richer-than (^J (proj₁ t)) 




-- Для справки.
-- ===========

-- Миры, в которых я мог бы оказаться, это НЕ миры, в которых я могу оказаться.


-- Миры, в которых я могу оказаться:
postulate
  _⇒_ : World → World → Set  -- "я могу оказаться в мире w2, если нахожусь в мире w1"


source : World → Set
source w = Σ World (λ x → x ⇒ w)  -- миры, из которых я мог попасть в w


-- Миры, в которых я мог бы оказаться.
-- Т.е. миры, в которых я могу оказаться из какого-то мира из 'source w1'.
_≈≈>_ : World → World → Set
w1 ≈≈> w2 = Σ (source w1) P
  where
  P : (source w1) → Set
  P x = (proj₁ x) ⇒ w2


-- If I were you, I wouldn’t bet on that horse.
-- If you were me, I wouldn’t bet on that horse.
-- I would be bolder if I weren’t me.
-- If I were you and you were me, I would be a rock star and you wouldn’t.

-- The rich could have all been poor
-- = there is a w in which all rich in w₀ are poor
module I4 where
  postulate
    w₀ : World
    D  : Set
    _is-in_      : D → World → Set

  Dw : World → Set
  Dw w = Σ[ x ∈ D ] x is-in w

  postulate
    _is-rich : ∀ {w} → Dw w → Set
    _is-poor : ∀ {w} → Dw w → Set

  -- actually rich
  act-rich = Σ[ x ∈ Dw w₀ ] x is-rich

  ea : act-rich → D
  ea ar = (proj₁ (proj₁ ar))

  -- any actually rich is poor in w (if he exists in it)
  P : World → Set
  P w = ∀ (ar : act-rich) (q : (ea ar) is-in w) → (ea ar , q) is-poor   
  
  P' : World → Set
  P' w = ∀ (ar : act-rich) → Σ[ q ∈ (ea ar) is-in w ] (ea ar , q) is-poor   
  
  s1 = ◇ w₀ P

  -- in full wording:
  s1f = Σ[ x ∈ (Σ[ w ∈ World ] (w₀ ≈> w)) ] ∀ (ar : act-rich) (q : (ea ar) is-in (proj₁ x)) → (ea ar , q) is-poor 
  
  s1' = ◇ w₀ P'

  -- in full wording:
  s1f' = Σ[ x ∈ (Σ[ w ∈ World ] (w₀ ≈> w)) ] ∀ (ar : act-rich) → Σ[ q ∈ (ea ar) is-in (proj₁ x) ] (ea ar , q) is-poor 
  
-- Necessarily, the rich could have all been poor.

  s2  = □ w₀ (λ w → ◇ w P)
  s2' = □ w₀ (λ w → ◇ w P')



-- There is a polar bear that could be bigger than any grizzly bear could
-- be if the grizzly bear were fatter than the polar bear really is.

-- Necessarily, the rich could have all been millionaires if they were poor
-- in reality.

