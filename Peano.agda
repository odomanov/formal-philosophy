-- Peano axioms
-- https://gist.github.com/IKEGAMIDaisuke/1211203
-- http://learnyouanagda.liamoc.net/pages/peano.html
-- https://plfa.github.io/Naturals/

{-----------------------------
    Аксиомы Пеано
    -------------
    1. 0 ∈ ℕ
    2. x ∈ ℕ => s(x) ∈ ℕ
    3. s(x) = s(y) <=> x = y
    4. ∀ x ¬ s(x) = 0
    5. Индукция
-------------------------------}

module Peano where

open import TTCore

data ℕ : Set where
  zero : ℕ        -- Ax 1
  suc  : ℕ → ℕ    -- Ax 2


-- Остальные аксиомы

-- Ax 3

ax3← : ∀ (n m : ℕ) → (n ≡ m) → (suc n ≡ suc m)
ax3← zero zero refl = refl
ax3← (suc n) _ refl = refl

ax3←₁ : ∀ (n m : ℕ) → (n ≡ m) → (suc n ≡ suc m)
ax3←₁ n _ refl = refl

ax3←₂ : ∀ {n m} → (n ≡ m) → (suc n ≡ suc m)
ax3←₂ refl = refl


ax3→ : ∀ (n m : ℕ) → (suc n ≡ suc m) → n ≡ m
ax3→ n m refl = refl

ax3→₂ : ∀ {n m} → (suc n ≡ suc m) → n ≡ m
ax3→₂ refl = refl



-- Ax 4

0≢1+n : ∀ {n} → zero ≢ suc n    -- ∀ {n} → zero ≡ suc n → ⊥
0≢1+n ()

1+n≢0 : ∀ {n} → suc n ≢ zero    -- ∀ {n} → suc n ≡ zero → ⊥
1+n≢0 ()


-- Ax 5. Induction

-- the best
ind : (P : ℕ → Set)
      → P zero
      → (∀ {n} → P n → P (suc n))
      → (∀ m → P m)
ind _ z _  zero   = z
ind P z f (suc n) = f (ind P z f n)


ind₁ : ∀ (P : ℕ → Set) → P zero → (∀ {n} → P n → P (suc n)) → (∀ n → P n)
ind₁ _ z _ zero    = z
ind₁ P z f (suc n) = ind₁ (λ z → P (suc z)) (f z) f n


ind₂ : ∀ {P : ℕ → Set} → P zero → (∀ {n} → P n → P (suc n)) → (∀ n → P n)
ind₂     z _ zero    = z
ind₂ {P} z f (suc n) = ind₂ {λ z → P (suc z)} (f z) f n





-- Операции с числами

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc n + m = suc (n + m)



-- Отношения на числах

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {n m} → n ≤ m → suc n ≤ suc m


_ : suc zero ≤ suc (suc zero)
_ = s≤s z≤n



_<_ : ℕ → ℕ → Set
x < y = suc x ≤ y

_≥_ : ℕ → ℕ → Set
x ≥ y = y ≤ x

_>_ : ℕ → ℕ → Set
x > y = y < x

_ : suc (suc zero) > suc zero
_ = s≤s (s≤s z≤n)


-- Второе возможное определение >
_≰_ : ℕ → ℕ → Set
x ≰ y = ¬ (x ≤ y)


-- Эквивалентны ли два определения > ?
-- Докажем только в одну сторону

prf : ∀ {x y} → x > y → x ≰ y     -- ∀ {x y} → x > y → x ≤ y → ⊥
-- prf {zero} {zero} ()
-- prf {zero} {suc n} ()
-- prf {suc n} {zero} _ ()
prf {suc n} {suc m} (s≤s x) (s≤s y) = prf x y 

-- prf2 : ∀ {x y} → x ≰ y → x > y     -- ∀ {x y} → (x ≤ y → ⊥) → x > y 
-- prf2 {zero} {zero} f = {!!}
--   where
--   zz : (zero ≰ zero) → ⊥
--   zz z = z z≤n
-- prf2 {zero} {suc n} f = {!!}
-- prf2 {suc n} {zero} f = s≤s z≤n
-- prf2 {suc n} {suc m} f = s≤s (prf2 (λ z → f (s≤s z)))


-- Максимум

max : ℕ → ℕ → ℕ
max zero n = n
max (suc n) zero = suc n
max (suc n) (suc m) = suc (max n m)




-- Разрешимое равенство

open import Agda.Builtin.Bool

_==_ : ℕ → ℕ → Bool
zero  == zero  = true
suc n == suc m = n == m
_ == _         = false



-- Разрешимое неравенство

_≤≤_ : ℕ → ℕ → Bool
zero ≤≤ n      = true
suc n ≤≤ suc m = n ≤≤ m
_ ≤≤ _         = false
