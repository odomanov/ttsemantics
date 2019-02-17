
module Monad.Maybe where

open import Agda.Primitive

open import Monad.Identity
open import Monad public

data Maybe {a} (A : Set a) : Set a where
  nothing : Maybe A
  just    : A → Maybe A

maybe : ∀ {a b} {A : Set a} {B : Set b} → B → (A → B) → Maybe A → B
maybe z f nothing  = z
maybe z f (just x) = f x

record MaybeT {a} (M : ∀ {ℓ} → Set ℓ → Set ℓ) (A : Set a) : Set a where
  no-eta-equality
  constructor maybeT
  field
    runMaybeT : M (Maybe A)

open MaybeT public

module _ {M : ∀ {ℓ} → Set ℓ → Set ℓ} where

  module _ {{_ : Monad M}} where

    private
      retMaybeT : ∀ {a} {A : Set a} → A → MaybeT M A
      runMaybeT (retMaybeT a) = return (just a)
      bindMaybeT : ∀ {a b} {A : Set a} {B : Set b}
        → MaybeT M A → (A → MaybeT M B) → MaybeT M B
      runMaybeT (bindMaybeT m f) = do
        just x ← runMaybeT m
          where nothing → return nothing
        runMaybeT (f x)

    instance
      MonadMaybeT : Monad (MaybeT M)
      return {{MonadMaybeT}} = retMaybeT
      _>>=_  {{MonadMaybeT}} = bindMaybeT

    liftMaybeT : ∀ {a} → {A : Set a} → M A → MaybeT M A
    runMaybeT (liftMaybeT m) = just <$> m

--- Monad ---

instance
  MonadMaybe : Monad Maybe
  return {{MonadMaybe}} a = just a
  _>>=_  {{MonadMaybe}} m f = maybe nothing f m
