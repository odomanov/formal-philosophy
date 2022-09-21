-- Объединение интенсионалов

module Multi where

open import Data.Empty using (⊥; ⊥-elim)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Intensional 


-- Intensional / World

data World : Set where
  w1 w2 : World

∧W : ∀ {i} (W : Set i) → Set i
∧W A = Intensional World A 

infixl 5 _>>=W_

_>>=W_ = _>>=_ World
∨W = getFunction World           -- extensional
-- extension in the world w
∨W_/_ : ∀ {ℓ} {A : Set ℓ} → ∧W A → World → A
∨W ma / w = ∨W ma w   --  getFunction World ma w
rigidW = return World
liftMW = liftM World

infixl 5 _⋆_

_⋆_ : ∀ {i k} {A : Set i} {B : Set k} → ∧W A → (A → B) → ∧W B
ma ⋆ f = liftMW f ma 


-- Intensional / Human    -- belief

data Human : Set where
  John Mary Bill Unknown : Human

∧H : ∀ {i} (W : Set i) → Set i
∧H A = Intensional Human A 

infixl 5 _>>=H_

_>>=H_ = _>>=_ Human
∨H = getFunction Human
rigidH = return Human
liftMH = liftM Human


-- the tallest human

itH : ∧W Human  
itH w1 = John
itH w2 = Mary


-- Example: dependent types

-- Run is not intensional but can be applied to intensions

postulate
  Run : ∧H Set    
  Jrp : Run John   -- a proof that John runs
  Brp : Run Bill
  Mr⊥ : Run Mary → ⊥
  
_ : (∨H Run) John ≡ Run John
_ = refl

_ : (∨H Run) John 
_ = Jrp

_ : (∨H Run) Mary → ⊥ 
_ = Mr⊥





-- playing with ∧H as monadic -- what for ?

postulate
  _Loves_ : ∧H (∧H Set)
  MlJp : Mary Loves John
  MlBp : Mary Loves Bill
  JlMp : John Loves Mary
  JlB⊥ : John Loves Bill → ⊥
  JlJ⊥ : John Loves John → ⊥
  l⊥ : ∀ (h : Human) → h Loves h → ⊥

_ : (∨H _Loves_) Mary John ≡ (Mary Loves John)
_ = refl

_ : (∨H ((rigidH Mary) >>=H _Loves_)) John ≡ (Mary Loves John)
_ = refl

_ : (∨H ((rigidH John) >>=H _Loves_)) Bill → ⊥
_ = JlB⊥

-- ???
_ : (∨H (liftMH (liftMH (λ x → _Loves_ x) (rigidH Mary)) (rigidH Mary)))
      Mary John ≡ (Mary Loves John)
_ = refl


_ : (∨W (liftMW (liftMH (liftMH _Loves_ (rigidH Mary)) (rigidH Mary)) itH) / w2) John
        ≡ (Mary Loves John)
_ = refl

-- ???
_ : (∨W (liftMW (liftMH (liftMH (λ x → _Loves_ x) (rigidH Mary)) (rigidH Mary)) itH) / w2) Mary → ⊥
_ = l⊥ Mary


-- Mary loves h
MaryLoves : ∧H Set
MaryLoves = λ h → Mary Loves h

_ : ∨W (liftMW MaryLoves itH) / w1 ≡ (Mary Loves John)
_ = refl

_ : ∨W (liftMW MaryLoves itH) / w2 → ⊥
_ = l⊥ Mary

_ : ∨W (liftMW MaryLoves (rigidW John)) / w2 ≡ (Mary Loves John)
_ = refl

_ : ∨W (itH ⋆ MaryLoves) / w1 ≡ (Mary Loves John)
_ = refl

_ : ∨W (itH ⋆ MaryLoves) / w2 → ⊥
_ = l⊥ Mary

_ : ∨W ((rigidW John) ⋆ MaryLoves) / w2 ≡ (Mary Loves John)
_ = refl

iMaryLoves : ∧H (∧W Set)
iMaryLoves = rigidW ∘ MaryLoves

_ : ∨W (itH >>=W iMaryLoves) / w1 ≡ (Mary Loves John)
_ = refl

_ : ∨W (itH >>=W iMaryLoves) / w2 → ⊥
_ = l⊥ Mary

-- ???
_ : ∀ (h : Human) → (∨W (liftMW (liftMH _Loves_ (rigidH Mary) h) itH) / w1
     ≡ (Mary Loves John))
_ = λ h → refl




