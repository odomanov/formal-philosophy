-- Используем Intensional.agda

module ModalLogic where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product -- using (_×_; proj₁; proj₂; Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)


data World : Set where
  w₁ w₂ : World
  
open import Intensional World

∧ = Intensional 

-- extensional
∨ : ∀ {a} {A : Set a} → ∧ A → World → A
∨ = getFunction 

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


-- Необходимо / возможно в мире w
□ : World → ∧ Set → Set
□ w₀ P = ∀ (x : acc w₀)  → ∨ P (proj₁ x)

◇ : World → ∧ Set → Set
◇ w₀ P = Σ[ x ∈ acc w₀ ] ∨ P (proj₁ x)

-- Необходимо / возможно в любом / каком-то мире 
□' : ∧ Set → Set
□' P = ∀ w → ∨ P w

◇' : ∧ Set → Set
◇' P = Σ[ w ∈ World ] ∨ P w


---------------------------------------------------------------------
-- Example: intension for the tallest human

data Human : Set where
  John Mary Bill : Human

-- the tallest human
itH : World → Human  
itH w₁ = John
itH w₂ = Mary

postulate
  Run'_/_ : Human → World → Set
  Jr1 : Run' John / w₁             -- John runs in w₁
  Mr2 : Run' Mary / w₂             -- Mary runs in w₂
  Jr2⊥ : Run' John / w₂ → ⊥

iRun' : Human → (∧ Set)
iRun' h = λ w → Run' h / w

_ : ∨ (itH >>= iRun') w₁ 
_ = Jr1

_ : ∨ (itH >>= iRun') w₂ 
_ = Mr2


-- the tallest human necessarily runs

_ : □' (itH >>= iRun') 
_ = prf
  where 
  prf : (w : World) → ∨ (itH >>= iRun') w 
  prf w₁ = Jr1
  prf w₂ = Mr2

-- другая запись
_ : □' (itH >>= iRun') 
_ = λ { w₁ → Jr1
      ; w₂ → Mr2
      }

_ : □ w₁ (itH >>= iRun')
_ = λ x → prf (proj₁ x)
  where 
  prf : (w : World) → ∨ (itH >>= iRun') w 
  prf w₁ = Jr1
  prf w₂ = Mr2

_ : □ w₂ (itH >>= iRun')
_ = prf
  where 
  prf : (w : acc w₂) → ∨ (itH >>= iRun') (proj₁ w) 
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


