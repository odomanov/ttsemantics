
module Monad.Identity where

open import Agda.Primitive
open import Monad

record Identity {a} (A : Set a) : Set a where
  constructor mkIdentity
  field
    runIdentity : A

open Identity public

instance

  MonadId : Monad Identity
  runIdentity (return {{MonadId}} x) = x
  _>>=_ {{MonadId}} m f = f (runIdentity m)

