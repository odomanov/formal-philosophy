module TTCore where

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
    
-- пустой тип
data ⊥ : Set where

-- всегда истинный тип
data ⊤ : Set where
  tt : ⊤

-- Отрицание
infix 3 ¬_
¬_ : Set → Set 
¬ P = P → ⊥


infix 4 _≢_
_≢_ : {A : Set} → A → A → Set 
x ≢ y = ¬ x ≡ y


