
module Monad.Identity where

open import Agda.Primitive
open import Monad

record Identity {a} (A : Set a) : Set a where
  constructor mkIdentity
  field
    runIdentity : A

open Identity public

instance
--   FunctorId : ∀ {a} → Functor (Identity {a})
--   runIdentity (fmap {{FunctorId}} f m) = f (runIdentity m)

--   ApplicativeId : ∀ {a} → Applicative (Identity {a})
--   runIdentity (pure {{ApplicativeId}} x) = x
--   runIdentity (_<*>_ {{ApplicativeId}} mf mx) = runIdentity mf (runIdentity mx)

  MonadId : Monad Identity
  runIdentity (return {{MonadId}} x) = x
  _>>=_ {{MonadId}} m f = f (runIdentity m)

--   FunctorId′ : ∀ {a b} → Functor′ {a} {b} Identity
--   runIdentity (fmap′ {{FunctorId′}} f m) = f (runIdentity m)

--   ApplicativeId′ : ∀ {a b} → Applicative′ {a} {b} Identity
--   runIdentity (pure′  {{ApplicativeId′}} x) = x
--   runIdentity (_<*>′_ {{ApplicativeId′}} mf mx) = runIdentity mf (runIdentity mx)

--   MonadId′ : ∀ {a b} → Monad′ {a} {b} Identity
--   _>>=′_ {{MonadId′}} m f = f (runIdentity m)

--   FoldableId : ∀ {a w} → Foldable {w = w} (Identity {a})
--   foldMap {{FoldableId}} f m = f (runIdentity m)

--   TraversableId : ∀ {a} → Traversable (Identity {a})
--   traverse {{TraversableId}} f m = pure mkIdentity <*> f (runIdentity m)
