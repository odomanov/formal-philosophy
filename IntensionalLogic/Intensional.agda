-- Monad for intensional values.
-- W is a type of possible worlds.

module Intensional (W : Set) where

open import Agda.Builtin.Bool
open import Data.String  
open import Function  using (id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

-- Monad for indexed functor (to take into account dependent types).
-- A variant of the Reader monad actually.

module Monad
    {M : ∀ {i} → Set i -> Set i}  
    (ret  : ∀ {i} → {A : Set i} -> A -> M A)
    (bind : ∀ {i k} → {A : Set i} {B : Set k} -> M A -> (A -> M B) -> M B)
  where

  infixl 5 _>>=_ _>>_
  infixl 40 _<$>_ _<*>_
  
  _>>=_ : ∀ {i k} → {A : Set i} {B : Set k} -> M A -> (A -> M B) -> M B
  _>>=_ = bind
  
  return : ∀ {i} → {A : Set i} -> A -> M A
  return = ret

  -- TODO check these definitions; they could be incorrect
  
  _>>_ : ∀ {i k} → {A : Set i} {B : Set k} -> M A -> M B -> M B
  m₁ >> m₂ = m₁ >>= \_ -> m₂
  
  _<*>_ : ∀ {i k} → {A : Set i} {B : Set k} -> M (A -> B) -> M A -> M B
  mf <*> mx = mf >>= \f -> mx >>= \x -> return (f x)

  -- fmap
  _<$>_ : ∀ {i k} → {A : Set i} {B : Set k} -> (A -> B) -> M A -> M B
  f <$> m = return f <*> m

  join : ∀ {i} {A : Set i} → M (M A) → M A
  join mma = mma >>= id

  liftM : ∀ {i k} → {A : Set i} {B : Set k} → (A → B) → M A → M B
  liftM f ma = ma >>= (return ∘ f)

  liftM2 : ∀ {i j k} → {A : Set i} {B : Set j} {C : Set k} →
    (A → B → C) → M A → M B → M C
  liftM2 f ma mb = ma >>= λ x → mb >>= λ y → return (f x y)



-- Let's define the type of intensionality.
-- The Reader datatype actually
Intensional : ∀ {ℓ} (A : Set ℓ) → Set ℓ
Intensional A = W → A

-- cf. runReader 
getFunction : ∀ {ℓ} {A : Set ℓ} → Intensional A → (W → A)
getFunction f = f

private
  ret : ∀ {i} {A : Set i} → A → Intensional {i} A
  ret = λ a → (λ _ → a)
  bind : ∀ {i k} → {A : Set i} → {B : Set k} →
    Intensional {i} A → (A → Intensional {k} B) → Intensional {k} B
  bind  = λ p f → (λ w → getFunction (f (getFunction p w)) w)

module IntMonad = Monad ret bind

open IntMonad public

-- Let's check the Monad Laws 

unitl : ∀ {i k} {A : Set i} {B : Set k} {a : A} {f : A → Intensional B}
  → ((return a) >>= f) ≡ f a
unitl = refl

unitr : ∀ {i} {A : Set i} {ma : Intensional A}
  → (ma >>= return) ≡ ma
unitr = refl

assoc : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} →
  {ma : Intensional A} {f : A → Intensional B} {g : B → Intensional C} → 
  ((ma >>= f) >>= g) ≡ (ma >>= (λ a → f a >>= g))
assoc = refl
    
