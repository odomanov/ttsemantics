-- Melissa and Naomi talking

module MelissaNaomi where

open import Data.Empty using (⊥)
open import Data.Product using (Σ-syntax; _,_)
open import Data.String using (String)
open import Data.Unit using (⊤)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; subst; sym)

open import Coercion

postulate
  LOC TIM : Set

-- Пример. Devlin, p. 610 sqq

postulate
  Human Door Object SIT Referable : Set

-- some coercions

postulate
  fDO : Door → Object
  fHO : Human → Object
  fOR : Object → Referable

instance
  DOc : Door <: Object
  DOc = coerce fDO
  HOc : Human <: Object
  HOc = coerce fHO
  OOc : Object <: Object
  OOc = identityCoercion
  ORc : Object <: Referable
  ORc = coerce fOR
  DRc : Door <: Referable
  DRc = coerce (fOR ∘ fDO)
  HRc : Human <: Referable
  HRc = coerce (fOR ∘ fHO)
  HHc : Human <: Human
  HHc = identityCoercion
  Stc : ∀ {a} → Set a <: Set a
  Stc = identityCoercion

postulate
  _refers-to_via_/_,_ : Human → Referable → String → LOC → TIM → Set
  _speaks-to_/_,_     : Human → Human → LOC → TIM → Set
  _utters_/_,_        : Human → String → LOC → TIM → Set


-- someone uttering a phrase, speaking to someone
record SitUttering : Set where
  constructor mkSitUttering
  field
    {l} : LOC
    {t} : TIM
    {speaker}  : Human
    {listener} : Human
    {phr} : String
    spk   : speaker speaks-to listener / l , t
    utt   : speaker utters phr / l , t

open SitUttering {{...}} public

-- reference situations

-- Someone refers when utters something.
record SitRef : Set where
  field
    situ : SitUttering
  open SitUttering --public
  field
    {referent} : Referable
    {phrase}   : String -- not necessarily equal to SitUttering.phr
    referring  : (speaker situ) refers-to referent via phrase / l situ , t situ


-- someone utters 'I'
record SitI : Set where
  field
    situ : SitUttering
  open SitUttering --public
  field
    uI : phr situ ≡ "I"




-- Melissa speaks to Naomi "A man is at the door"

postulate
  _at-the-door_ : Human → Door → Set

-- described situation: a man at the door.
-- The type of situations described by the phrase "A man is at the door".
record SitManDoor : Set where
  field
    {man}   : Human
    {door}  : Door
    mandoor : man at-the-door door


module theSit where    -- Our situation

  postulate sitManDoor : SitManDoor
  open SitManDoor sitManDoor using (door) -- we don't know the man Melissa refers to

  Melissa-man     = SitManDoor.man     sitManDoor
  Melissa-mandoor = SitManDoor.mandoor sitManDoor

  postulate
    Melissa Naomi : Human
    sitUttering-mandoor : SitUttering
    s≡m  : SitUttering.speaker  sitUttering-mandoor ≡ Melissa
    l≡n  : SitUttering.listener sitUttering-mandoor ≡ Naomi
    p≡md : SitUttering.phr      sitUttering-mandoor ≡ "A man is at the door"
  loc = SitUttering.l sitUttering-mandoor
  tim = SitUttering.t sitUttering-mandoor
  postulate
    mrefd : Melissa refers-to ⟪ door ⟫ via "door" / loc , tim
    mrefm : Melissa refers-to ⟪ Melissa-man ⟫  via "man"  / loc , tim


  _ : Σ[ x ∈ Human ] x at-the-door door
  _ = Melissa-man , Melissa-mandoor

  _ : Σ[ x ∈ Human ] Σ[ y ∈ Door ] x at-the-door y
  _ = Melissa-man , door , Melissa-mandoor

  -- the type of Humans Melissa refers to
  _ : Σ[ x ∈ Human ] Σ[ p ∈ String ] Σ[ l ∈ LOC ] Σ[ t ∈ TIM ]
      Melissa refers-to ⟪ x ⟫ via p / l , t
  _ = Melissa-man , "man" , loc , tim , mrefm

  -- Melissa refers to door (when speaks to Naomi)
  MrD : SitRef
  MrD = record
        { situ = sitUttering-mandoor
        ; referring =
            subst (λ x → x refers-to ⟪ door ⟫ via "door" / loc , tim)
            (sym s≡m) mrefd
        }

  -- Melissa refers to man (when speaks to Naomi)
  MrM : SitRef
  MrM = record
        { situ = sitUttering-mandoor
        ; referring =
            subst (λ x → x refers-to ⟪ Melissa-man ⟫ via "man" / loc , tim)
            (sym s≡m) mrefm
        }





  -- Defining meaning ---------------------------------


  postulate
    Meaning : Set
    fRM  : Referable → Meaning

  -- What meaning can be:
  instance
    RMc : Referable <: Meaning
    RMc = coerce fRM
    OMc : Object <: Meaning
    OMc = coerce (fRM ∘ fOR)
    DMc : Door <: Meaning
    DMc = coerce (fRM ∘ fOR ∘ fDO)
    HMc : Human <: Meaning
    HMc = coerce (fRM ∘ fOR ∘ fHO)
    MMc : Meaning <: Meaning
    MMc = identityCoercion
    RRc : Referable <: Referable
    RRc = identityCoercion

  -- The situation in which someone utters a phrase that means something.
  -- Simple uttering cannot be meaningful, there should be some reference.
  record SitMeaning (A : Set) : Set where
    field
      sitmu   : A → SitUttering
      meaning : A → Referable -- Meaning

  open SitMeaning {{...}} public

  -- abstract meaning
  instance
    SMRef : SitMeaning SitRef
    sitmu   {{SMRef}}   = SitRef.situ
    meaning {{SMRef}} s = ⟪ SitRef.referent s ⟫

  -- meaning-in-use
  _ : meaning MrD ≡ ⟪ door ⟫
  _ = refl

  _ : meaning MrM ≡ ⟪ Melissa-man ⟫
  _ = refl

  -- but we don't need to define MrD or MrM:
  _ : meaning record
              { situ = sitUttering-mandoor
              ; referring =
                  subst (λ x → x refers-to ⟪ door ⟫ via "door" / loc , tim)
                  (sym s≡m) mrefd
              }
              ≡ ⟪ door ⟫
  _ = refl


  -- abstract meaning = the speaker of SitI
  instance
    SMI : SitMeaning SitI
    sitmu   {{SMI}}   = SitI.situ
    meaning {{SMI}} s = ⟪ SitUttering.speaker (SitI.situ s) ⟫

  postulate
    sitUttering-I : SitUttering
    s≡mI  : SitUttering.speaker  sitUttering-I ≡ Melissa
    p≡mdI : SitUttering.phr      sitUttering-I ≡ "I"

  -- meaning-in-use
  -- the meaning of 'I' = Melissa
  _ : meaning record
              { situ = sitUttering-I
              ; uI = p≡mdI
              }
              ≡ ⟪ Melissa ⟫
  _ = ≡-coerce s≡mI


  -- Situations as meaning.

  postulate
    fSR   : SIT → Referable
    fMDS : SitManDoor → SIT

  instance
    SRc : SIT <: Referable
    SRc = coerce fSR
    SMc : SIT <: Meaning
    SMc = coerce (fRM ∘ fSR)
    SSc : SIT <: SIT
    SSc = identityCoercion
    MDSc : SitManDoor <: SIT
    MDSc = coerce fMDS
    MDRc : SitManDoor <: Referable
    MDRc = coerce (fSR ∘ fMDS)
    MDMc : SitManDoor <: Meaning
    MDMc = coerce (fRM ∘ fSR ∘ fMDS)

  -- Melissa utters 'Man at the door'
  postulate
    mref-mandoor : SitUttering.speaker sitUttering-mandoor
                   refers-to ⟪ sitManDoor ⟫ via "A man is at the door"
                   / loc , tim

  instance
    SMSIT : SitMeaning SitRef
    sitmu {{SMSIT}} = SitRef.situ
    meaning {{SMSIT}} s = ⟪ SitRef.referent s ⟫

  _ : meaning record
              { situ = sitUttering-mandoor
              ; referring = mref-mandoor
              }
              ≡ ⟪ sitManDoor ⟫
  _ = refl






-- -- Resource situations

-- -- Melissa utters "The man I saw running yesterday is at the door"

-- postulate
--   _runs/_ : Human → TIM → Set
--   yesterday : TIM

-- -- Resource situation "a man running yesterday"
-- record man-runs : Set where
--   field
--     man  : Human
--     mrun : man runs/ yesterday

-- -- open man-runs

-- record MsNr : Set where
--   open man-runs
--   field
--     loc    : LOC
--     tim   : TIM
--     sit-mr : man-runs
--     door   : Door
--     mandoor    : at-the-door (man sit-mr) door
--     phrase : String
--     utters : Melissa utters phrase to Naomi / loc , tim
--     refm   : Melissa refers-to ⟪ man sit-mr ⟫ via MAN / loc , tim
--     refd   : Melissa refers-to ⟪ door ⟫ via DOOR / loc , tim

