module ModalLogic where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product -- using (_×_; proj₁; proj₂; Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)


open import Monad.Identity
open import Monad.Reader   

data World : Set where
  w₁ w₂ : World
  
IntMonad = MonadReader World

-- intensional
∧ : ∀ {a} (A : Set a) → Set a
∧ A = Reader World A

-- extensional
∨ : ∀ {a} {A : Set a} → ∧ A → World → A
∨ = runReader                 

-- extension in the world w
∨_/_ : ∀ {a} {A : Set a} → ∧ A → World → A
∨ ma / w = ∨ ma w  

rigid = return 

infixl 5 _⋆_

-- simple lifting
_⋆_ : ∀ {i k} {A : Set i} {B : Set k} → ∧ A → (A → B) → ∧ B
ma ⋆ f = liftM f ma 



-- Accessibility

infix 5 _≈>_

_≈>_ : World → World → Set
W₁ ≈> W₂ = ⊤
-- _  ≈> _  = ⊥

-- accessible from w₀
acc : World → Set
acc w₀ = Σ[ w ∈ World ] w₀ ≈> w


□ : World → ∧ Set → Set
□ w₀ P = ∀ (x : acc w₀)  → runReader P (proj₁ x)
-- □ : ∧ (∧ Set → Set)
-- □ = mkReaderT (λ w₀ → mkIdentity (λ P → ∀ (x : acc w₀)  → runReader P (proj₁ x)))

◇ : World → ∧ Set → Set
◇ w₀ P = Σ[ x ∈ acc w₀ ] runReader P (proj₁ x)

□' : ∧ Set → Set
□' P = ∀ w → runReader P w

◇' : ∧ Set → Set
◇' P = Σ[ w ∈ World ] runReader P w

-- □' : ∀ {i} {A : Set (lsuc i)} → World → ∧ A → Set i
-- □' w₀ P = ∀ (x : acc w₀)  → P (proj₁ x)

-- ◇' : ∀ {i} {A : Set i} → World → ∧ A → Set
-- ◇' w₀ P = Σ[ x ∈ acc w₀ ] P (proj₁ x)

---------------------------------------------------------------------
-- Example: intension for the tallest human

data Human : Set where
  John Mary Bill : Human

-- wrap a function from World into intensional 
mkIntensional : ∀ {a} {A : Set a} → (World → A) → ∧ A
mkIntensional f = mkReaderT (λ w → mkIdentity (f w))

itH = mkIntensional f
  where
  f : World → Human  
  f w₁ = John
  f w₂ = Mary


postulate
  Run'_/_ : Human → World → Set
  Jr1 : Run' John / w₁             -- John runs in w₁
  Mr2 : Run' Mary / w₂             -- Mary runs in w₂
  Jr2⊥ : Run' John / w₂ → ⊥

iRun' : Human → (∧ Set)
iRun' h = mkIntensional (λ w → Run' h / w)

_ : ∨ (itH >>= iRun') w₁ 
_ = Jr1

_ : ∨ (itH >>= iRun') w₂ 
_ = Mr2


-- the tallest human necessarily runs

_ : □' (itH >>= iRun') 
_ = prf
  where 
  prf : (w : World) → (∨ (itH >>= iRun') w) 
  prf w₁ = Jr1
  prf w₂ = Mr2

_ : □' (itH >>= iRun') 
_ = λ { w₁ → Jr1
      ; w₂ → Mr2
      }

_ : □ w₁ (itH >>= iRun')
_ = λ x → prf (proj₁ x)
  where 
  prf : (w : World) → (∨ (itH >>= iRun') w) 
  prf w₁ = Jr1
  prf w₂ = Mr2

  -- _ : □' w₁ (Император ★ iБежит)
  -- _ = prf where 
  --   prf : (w : acc w₁) → (∨ (Император ★ iБежит) (proj₁ w)) 
  --   prf (w₁ , _) = Jr1
  --   prf (w₂ , _) = Mr2
  
_ : □ w₂ (itH >>= iRun')
_ = prf
  where 
  prf : (w : acc w₂) → (∨ (itH >>= iRun') (proj₁ w)) 
  prf (w₁ , _) = Jr1
  prf (w₂ , _) = Mr2


-- the tallest human possibly runs

_ : ◇' (itH >>= iRun') 
_ = w₁ , Jr1

-- another proof
_ : ◇' (itH >>= iRun') 
_ = w₂ , Mr2

_ : ◇ w₁ (itH >>= iRun')
_ = (w₂ , _) , Mr2

