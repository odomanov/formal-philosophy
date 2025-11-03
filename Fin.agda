module Fin where

open import TTCore
open import Nat hiding (_+_)


-- Fin n is a type with n elements -- numbers less than n.

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} (i : Fin n) → Fin (suc n)



toℕ : ∀ {n} → Fin n → ℕ
toℕ zero = zero
toℕ (suc i) = suc (toℕ i)

fromℕ : (n : ℕ) → Fin (suc n)   
fromℕ zero    = zero
fromℕ (suc n) = suc (fromℕ n)

_+_ : ∀ {m n} (i : Fin m) (j : Fin n) → Fin (toℕ i Nat.+ n)
zero  + j = j
suc i + j = suc (i + j)

-- lift function
liftfun : ∀ {m n} k → (Fin m → Fin n) → Fin (k Nat.+ m) → Fin (k Nat.+ n)
liftfun zero    f i       = f i
liftfun (suc k) f zero    = zero
liftfun (suc k) f (suc i) = suc (liftfun k f i)

