-- Peano axioms
-- https://gist.github.com/IKEGAMIDaisuke/1211203
-- http://learnyouanagda.liamoc.net/pages/peano.html
-- https://plfa.github.io/Naturals/

--  Аксиомы Пеано
--  -------------
--  1. 0 ∈ ℕ
--  2. x ∈ ℕ => s(x) ∈ ℕ
--  3. s(x) = s(y) <=> x = y
--  4. ∀ x ¬ s(x) = 0
--  5. Индукция


module Peano where

open import TTCore

data ℕ : Set where
  zero : ℕ        -- Ax 1
  suc  : ℕ → ℕ    -- Ax 2


-- Остальные аксиомы

-- Ax 3

ax3← : ∀ (n m : ℕ) → (n ≡ m) → (suc n ≡ suc m)
ax3← zero zero _ = refl
ax3← (suc n) _ refl = refl

ax3←₁ : ∀ (n m : ℕ) → (n ≡ m) → (suc n ≡ suc m)
ax3←₁ n .n refl = refl

ax3←₂ : ∀ (n m : ℕ) → (n ≡ m) → (suc n ≡ suc m)
ax3←₂ _ _ refl = refl


ax3→ : ∀ (n m : ℕ) → (suc n ≡ suc m) → n ≡ m
ax3→ n m refl = refl

ax3→₂ : ∀ (n m : ℕ) → (suc n ≡ suc m) → n ≡ m
ax3→₂ _ _ refl = refl



-- Ax 4

0≢1+n : ∀ {n} → zero ≢ suc n
0≢1+n ()

1+n≢0 : ∀ {n} → suc n ≢ zero
1+n≢0 ()


-- induction

-- the best
ind₄ : (P : ℕ → Set)
       → P zero
       → (∀ {n} → P n → P (suc n))
       → (∀ m → P m)
ind₄ _ z _  zero   = z
ind₄ P z f (suc n) = f {n} (ind₄ P z f n)


ind : ∀ (P : ℕ → Set) → P zero → (∀ {n} → P n → P (suc n)) → (∀ n → P n)
ind _ z _ zero     = z
ind P z f (suc n) = ind (λ z → P (suc z)) (f z) f n


ind₁ : ∀ {P : ℕ → Set} → P zero → (∀ {n} → P n → P (suc n)) → (∀ n → P n)
ind₁     z _ zero     = z
ind₁ {P} z f (suc n) = ind₁ {λ z → P (suc z)} (f z) f n


ind₂ : ∀ (P : ℕ → Set) (m : ℕ) → P zero → (∀ {n} → P n → P (suc n)) → P m
ind₂ _  zero    z _ = z
ind₂ P (suc n) z f = ind₂ (λ z → P (suc z)) n (f z) f

