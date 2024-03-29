module Nat where

open import TTCore

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat public
  using (zero; suc) renaming (Nat to ℕ)
open import Agda.Builtin.Nat public
  using () renaming (_==_ to _≡ᵇ_; _<_ to _<ᵇ_)

infix 4 _≤_ _<_ _≥_ _>_ _≰_ _≮_ _≱_ _≯_

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n}                 → zero  ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n

_<_ : ℕ → ℕ → Set
m < n = suc m ≤ n

_≥_ : ℕ → ℕ → Set
m ≥ n = n ≤ m

_>_ : ℕ → ℕ → Set
m > n = n < m

_≰_ : ℕ → ℕ → Set
a ≰ b = ¬ a ≤ b

_≮_ : ℕ → ℕ → Set
a ≮ b = ¬ a < b

_≱_ : ℕ → ℕ → Set
a ≱ b = ¬ a ≥ b

_≯_ : ℕ → ℕ → Set
a ≯ b = ¬ a > b


open import Agda.Builtin.Nat public
  using (_+_; _*_) renaming (_-_ to _∸_)

pred : ℕ → ℕ
pred zero    = zero
pred (suc n) = n


-- infixl 7 _⊓_
-- infixl 6 _+⋎_ _⊔_

-- -- Argument-swapping addition. Used by Data.Vec._⋎_.

-- _+⋎_ : ℕ → ℕ → ℕ
-- zero  +⋎ n = n
-- suc m +⋎ n = suc (n +⋎ m)

-- -- Max.

-- _⊔_ : ℕ → ℕ → ℕ
-- zero  ⊔ n     = n
-- suc m ⊔ zero  = suc m
-- suc m ⊔ suc n = suc (m ⊔ n)

-- -- Min.

-- _⊓_ : ℕ → ℕ → ℕ
-- zero  ⊓ n     = zero
-- suc m ⊓ zero  = zero
-- suc m ⊓ suc n = suc (m ⊓ n)

-- -- Division by 2, rounded downwards.

-- ⌊_/2⌋ : ℕ → ℕ
-- ⌊ 0 /2⌋           = 0
-- ⌊ 1 /2⌋           = 0
-- ⌊ suc (suc n) /2⌋ = suc ⌊ n /2⌋

-- -- Division by 2, rounded upwards.

-- ⌈_/2⌉ : ℕ → ℕ
-- ⌈ n /2⌉ = ⌊ suc n /2⌋

-- -- Naïve exponentiation

-- _^_ : ℕ → ℕ → ℕ
-- x ^ zero  = 1
-- x ^ suc n = x * x ^ n

-- -- Distance

-- ∣_-_∣ : ℕ → ℕ → ℕ
-- ∣ zero  - y     ∣ = y
-- ∣ x     - zero  ∣ = x
-- ∣ suc x - suc y ∣ = ∣ x - y ∣

-- ------------------------------------------------------------------------
-- -- The following, alternative definition of _≤_ is more suitable for
-- -- well-founded induction (see Induction.Nat).

-- infix 4 _≤′_ _<′_ _≥′_ _>′_

-- data _≤′_ (m : ℕ) : ℕ → Set where
--   ≤′-refl :                         m ≤′ m
--   ≤′-step : ∀ {n} (m≤′n : m ≤′ n) → m ≤′ suc n

-- _<′_ : ℕ → ℕ → Set
-- m <′ n = suc m ≤′ n

-- _≥′_ : ℕ → ℕ → Set
-- m ≥′ n = n ≤′ m

-- _>′_ : ℕ → ℕ → Set
-- m >′ n = n <′ m

-- ------------------------------------------------------------------------
-- -- Another alternative definition of _≤_.

-- record _≤″_ (m n : ℕ) : Set where
--   constructor less-than-or-equal
--   field
--     {k}   : ℕ
--     proof : m + k ≡ n

-- infix 4 _≤″_ _<″_ _≥″_ _>″_

-- _<″_ : ℕ → ℕ → Set
-- m <″ n = suc m ≤″ n

-- _≥″_ : ℕ → ℕ → Set
-- m ≥″ n = n ≤″ m

-- _>″_ : ℕ → ℕ → Set
-- m >″ n = n <″ m

-- ------------------------------------------------------------------------
-- -- Useful for induction when you have an upper bound.

-- data _≤‴_ : ℕ → ℕ → Set where
--   ≤‴-refl : ∀{m} → m ≤‴ m
--   ≤‴-step : ∀{m n} → suc m ≤‴ n → m ≤‴ n

-- infix 4 _≤‴_ _<‴_ _≥‴_ _>‴_

-- _<‴_ : ℕ → ℕ → Set
-- m <‴ n = suc m ≤‴ n

-- _≥‴_ : ℕ → ℕ → Set
-- m ≥‴ n = n ≤‴ m

-- _>‴_ : ℕ → ℕ → Set
-- m >‴ n = n <‴ m

