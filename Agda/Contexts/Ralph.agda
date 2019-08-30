-- Ralph -- Situation semantics through modules

open import Data.Empty using (⊥)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; subst) 
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)

module Ralph where

postulate
  Man : Set
  _is-a-spy : Man → Set


{- Если нам нужен метаязык, т.е. мы хотим говорить о ситуациях, то ситуация
   должна быть представлена как элемент (терм) некоторого типа.
   Поэтому вместо модулей мы переходим к записям.
   Записи это типы ситуаций.
-}


-- there is something of type A
record SitSmth (A : Set) : Set where
  constructor mkSitSmth
  field 
    smth : A

-- there is a man
record SitMan : Set where
  constructor mkSitMan
  field
    sitsmth : SitSmth Man
  open SitSmth sitsmth renaming (smth to man) public



-- See below a simpler version, without using SitMan.
-- But this version demonstrates that I can open SitMan.
module OneMan where

  -- there is a spy -- composed situation
  record SitSpy : Set where
    field
      sitMan : SitMan  -- man in a hat
    open SitMan sitMan public
    field
      man-spy : man is-a-spy

  -- Ralph's belief = SitSpy
  module RalphBelief where
    postulate
      sitSpy : SitSpy

    -- when SitSpy is not open
    _ : SitMan.man (SitSpy.sitMan sitSpy) is-a-spy
    _ = SitSpy.man-spy sitSpy

    open SitSpy sitSpy public  -- makes 'man' available.
                               -- This means that Ralph's belief = (an instance of) SitSpy.

    _ : man is-a-spy
    _ = man-spy


  -- proof in a local context (= Ralph's context)
  _ : Σ[ x ∈ Man ] x is-a-spy
  _ = man , man-spy 
      where
      open RalphBelief

  -- the same without 'open'
  _ : Σ[ x ∈ Man ] x is-a-spy
  _ = RalphBelief.man , RalphBelief.man-spy 


  -- we can also define SitSpy instead of postulating it
  module RalphBelief2 where
    postulate
      m : Man
      mspy : m is-a-spy
      
    sitSpy = record
             { sitMan = record { sitsmth = mkSitSmth m }
             ; man-spy = mspy
             }

    open SitSpy sitSpy public   -- makes 'man' available

    _ : man is-a-spy
    _ = man-spy 

  -- proof in a local context
  _ : Σ[ x ∈ Man ] x is-a-spy
  _ = man , man-spy 
      where
      open RalphBelief2

  -- the same without 'open'
  _ : Σ[ x ∈ Man ] x is-a-spy
  _ = RalphBelief2.man , RalphBelief2.man-spy





-- simplification of the previous ----------------------
--
module OneMan' where

  -- there is a spy
  record SitSpy : Set where
    field
      {man} : Man
      man-spy  : man is-a-spy

    _ : man is-a-spy
    _ = man-spy 


  -- modelling Ralph's belief
  --
  module RalphBelief where
    postulate
      sitSpy : SitSpy

    open SitSpy sitSpy public  -- now 'man' is available
                               -- This means that Ralph's belief = (an instance of) SitSpy.

    -- inside of Ralph's belief
    _ : man is-a-spy
    _ = man-spy


  -- proof in a local context (= Ralph's context)
  _ : Σ[ x ∈ Man ] x is-a-spy
  _ = man , man-spy 
      where
      open RalphBelief

  -- the same without 'open'
  _ : Σ[ x ∈ Man ] x is-a-spy
  _ = RalphBelief.man , RalphBelief.man-spy 


  -- we can also define SitSpy instead of postulating it.
  -- Proofs remain the same.
  module RalphBelief2 where
    postulate
      m : Man
      mspy : m is-a-spy
      
    open SitSpy record {man-spy = mspy} public   -- makes 'man' available

    _ : man is-a-spy
    _ = mspy 

  -- proof in a local context
  _ : Σ[ x ∈ Man ] x is-a-spy
  _ = man , mspy 
      where
      open RalphBelief2

  -- the same without 'open'
  _ : Σ[ x ∈ Man ] x is-a-spy
  _ = RalphBelief2.man , RalphBelief2.mspy



-- two men ---------------------------------
--  
module TwoMen where  -- our belief actually

  -- What means to believe that ...
  record SitTwo : Set where
    field
      {man-in-a-hat}     : Man 
      {man-on-the-beach} : Man
      hspy :   man-in-a-hat is-a-spy
      bspy : ¬ man-on-the-beach is-a-spy
      h≢b  :   man-in-a-hat ≢ man-on-the-beach

  -- модуль для доказательства того, во что верит Ральф
  module RalphBelief where
    postulate sit : SitTwo  -- this implies there are instances of Man
    open SitTwo sit public

    _ : man-in-a-hat is-a-spy
    _ = hspy 

    _ : ¬ man-on-the-beach is-a-spy
    _ = bspy 

    _ : Σ[ x ∈ Man ] ¬ x is-a-spy
    _ = man-on-the-beach , bspy 


  -- proof in a local context
  _ : Σ[ x ∈ Man ] ¬ x is-a-spy
  _ = man-on-the-beach , bspy 
      where
      open RalphBelief


  -- if we open the whole Ralph's belief we get a contradiction
  module OurBelief where
    open RalphBelief

    postulate
      Ortcutt : Man
      o≡h : Ortcutt ≡ man-in-a-hat 
      o≡b : Ortcutt ≡ man-on-the-beach 

    _ : ⊥
    _ = contradiction (trans (sym o≡h) o≡b) h≢b


  -- let's open 2 men only ---------------------------------
  --
  module OurBelief1 where      -- our belief
    open RalphBelief using (man-in-a-hat; man-on-the-beach)
    
    postulate
      Ortcutt : Man
      o≡h : Ortcutt ≡ man-in-a-hat 
      o≡b : Ortcutt ≡ man-on-the-beach 

    _ : Ortcutt is-a-spy
    _ = subst (λ x → x is-a-spy) (sym (proj₂ (proj₂ hs))) hspy
      where
        open RalphBelief
        hs : Σ[ x ∈ Man ] x is-a-spy × Ortcutt ≡ x
        hs = man-in-a-hat , hspy , o≡h

    _ : ¬ Ortcutt is-a-spy
    _ = subst (λ x → ¬ x is-a-spy) (sym (proj₂ (proj₂ ¬bs))) bspy
      where
        open RalphBelief
        ¬bs : Σ[ x ∈ Man ] ¬ x is-a-spy × Ortcutt ≡ x
        ¬bs = man-on-the-beach , bspy , o≡b

    -- So we can prove the contradiction.
    -- But we can prove it more directly:

    h≡b : man-in-a-hat ≡ man-on-the-beach 
    h≡b = trans (sym o≡h) o≡b

    -- We can prove contradiction only for Ralph's belief.
    -- Our belief that Ralph believes in h≢b doesn't imply that we believe in h≢b.
    -- Although our belief in man-in-a-hat and man-on-the-beach are the same as Ralph's.
    _ : ⊥
    _ = contradiction h≡b (RalphBelief.h≢b)

    -- the same using local context
    _ : ⊥
    _ = contradiction h≡b h≢b
        where open RalphBelief -- means that we fully agree with Ralph.



  -- open also that man-in-a-hat is a spy
  module OurBelief2 where                -- our belief
    open RalphBelief using (man-in-a-hat; man-on-the-beach; hspy)
    
    postulate
      Ortcutt : Man
      o≡h : Ortcutt ≡ man-in-a-hat 
      o≡b : Ortcutt ≡ man-on-the-beach 

    -- h≡b : man-in-a-hat ≡ man-on-the-beach 
    -- h≡b = trans (sym o≡h) o≡b

    -- no need to locally open RalphBelief
    _ : Σ[ x ∈ Man ] x is-a-spy 
    _ = man-in-a-hat , hspy 

    -- but here I need to open it
    _ : Σ[ x ∈ Man ] ¬ x is-a-spy 
    _ = man-on-the-beach , bspy 
      where open RalphBelief

    -- in particular, we can prove:
    _ : Ortcutt is-a-spy
    _ = subst (λ x → x is-a-spy) (sym (proj₂ (proj₂ hs))) hspy
      where
        hs : Σ[ x ∈ Man ] x is-a-spy × Ortcutt ≡ x
        hs = man-in-a-hat , hspy , o≡h
