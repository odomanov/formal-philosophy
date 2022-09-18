
module Monad.Maybe where

open import Agda.Primitive

open import Monad.Identity
open import Monad public

data Maybe {a} (A : Set a) : Set a where
  nothing : Maybe A
  just    : A → Maybe A

{-# FOREIGN GHC type AgdaMaybe l = Maybe #-}
{-# COMPILE GHC Maybe = data MAlonzo.Code.Prelude.Maybe.AgdaMaybe (Nothing | Just) #-}

maybe : ∀ {a b} {A : Set a} {B : Set b} → B → (A → B) → Maybe A → B
maybe z f nothing  = z
maybe z f (just x) = f x
{-# INLINE maybe #-}


record MaybeT {a} (M : ∀ {ℓ} → Set ℓ → Set ℓ) (A : Set a) : Set a where
  no-eta-equality
  constructor maybeT
  field
    runMaybeT : M (Maybe A)

open MaybeT public

module _ {M : ∀ {ℓ} → Set ℓ → Set ℓ} where

  -- instance
  --   FunctorMaybeT : {{_ : Functor M}} → Functor {a = a} (MaybeT M)
  --   runMaybeT (fmap {{FunctorMaybeT}} f m) = fmap f <$> runMaybeT m

  --   FunctorZeroMaybeT : {{_ : Monad M}} → FunctorZero {a = a} (MaybeT M)
  --   runMaybeT (empty {{FunctorZeroMaybeT}}) = return nothing

  --   AlternativeMaybeT : {{_ : Monad M}} → Alternative {a = a} (MaybeT M)
  --   runMaybeT (_<|>_ {{AlternativeMaybeT {{monadM}}}} mx my) = do
  --     just x ← runMaybeT mx
  --       where nothing → runMaybeT my
  --     return (just x)

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
      -- ApplicativeMaybeT : Applicative {a = a} (MaybeT M)
      -- runMaybeT (pure {{ApplicativeMaybeT}} x) = pure (just x)
      -- _<*>_ {{ApplicativeMaybeT}} = monadAp bindMaybeT

      MonadMaybeT : Monad (MaybeT M)
      return {{MonadMaybeT}} = retMaybeT
      _>>=_  {{MonadMaybeT}} = bindMaybeT

    liftMaybeT : ∀ {a} → {A : Set a} → M A → MaybeT M A
    runMaybeT (liftMaybeT m) = just <$> m

-- instance
--   TransformerMaybeT : ∀ {a} → Transformer {a} MaybeT
--   lift {{TransformerMaybeT}} = liftMaybeT


--- Monad ---

instance
  -- FunctorMaybe : ∀ {a} → Functor (Maybe {a})
  -- fmap {{FunctorMaybe}} f m = maybe nothing (just ∘ f) m

  -- ApplicativeMaybe : ∀ {a} → Applicative (Maybe {a})
  -- pure  {{ApplicativeMaybe}} = just
  -- _<*>_ {{ApplicativeMaybe}} mf mx = maybe nothing (λ f → fmap f mx) mf

  MonadMaybe : Monad Maybe
  return {{MonadMaybe}} a = just a
  _>>=_  {{MonadMaybe}} m f = maybe nothing f m

  -- FunctorMaybe′ : ∀ {a b} → Functor′ {a} {b} Maybe
  -- fmap′ {{FunctorMaybe′}} f m = maybe nothing (just ∘ f) m

  -- ApplicativeMaybe′ : ∀ {a b} → Applicative′ {a} {b} Maybe
  -- _<*>′_ {{ApplicativeMaybe′}} (just f) (just x) = just (f x)
  -- _<*>′_ {{ApplicativeMaybe′}}  _        _       = nothing

  -- MonadMaybe′ : ∀ {a b} → Monad′ {a} {b} Maybe
  -- _>>=′_ {{MonadMaybe′}} m f = maybe nothing f m
