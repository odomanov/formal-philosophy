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


-- Ax 5. Индукция

ind : (P : ℕ → Set)
      → P zero
      → (∀ {n} → P n → P (suc n))
      → (∀ m → P m)
ind _ z _  zero   = z
ind P z f (suc n) = f (ind P z f n)



-- Операции с числами

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc n + m = suc (n + m)

-- предыдущее число
pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n


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
-- Докажем в одну сторону

prf : ∀ {x y} → x > y → x ≰ y     -- ∀ {x y} → x > y → x ≤ y → ⊥
prf {suc _} {suc _} (s≤s x) (s≤s y) = prf x y 

-- а в другую?

prf2 : ∀ {x y} → x ≰ y → x > y     -- ∀ {x y} → (x ≤ y → ⊥) → x > y 
prf2 {zero} {y} p = {!!}           -- доказательства zero > y не существует
prf2 {suc x} {zero} p = s≤s z≤n
prf2 {suc x} {suc y} p = s≤s (prf2 (λ z → p (s≤s z)))



-- Теорема

t1 : (x y : ℕ) → x ≤ y → Σ[ z ∈ ℕ ] x + z ≡ y
t1 zero y p = y , refl
t1 (suc x) (suc y) (s≤s p) = let (xx , pp) = t1 x y p in xx , cong {x} {y} pp
  where
  cong : ∀ {x y z} → x + z ≡ y → suc (x + z) ≡ suc y
  cong refl = refl

-- Максимум

max : ℕ → ℕ → ℕ
max zero n = n
max (suc n) zero = suc n
max (suc n) (suc m) = suc (max n m)

-- TODO: Минимум



-- Разрешимое равенство

_≡ᵇ_ : ℕ → ℕ → Bool
zero  ≡ᵇ zero  = true
suc n ≡ᵇ suc m = n ≡ᵇ m
_ ≡ᵇ _         = false



-- Разрешимое неравенство

_≤ᵇ_ : ℕ → ℕ → Bool
zero ≤ᵇ n      = true
suc n ≤ᵇ suc m = n ≤ᵇ m
_ ≤ᵇ _         = false


-- Decidable types (разрешимые типы)

module dec1 where

  data Dec {A : Set} (rel : A → A → Set) : Set where
    yes : {x y : A} → rel x y → Dec rel
    no  : {x y : A} → ¬ rel x y → Dec rel
  
  _=?_ : ℕ → ℕ → Dec _≡_
  zero  =? zero  = yes {x = zero}  {y = zero}  refl
  zero  =? suc y = no  {x = zero}  {y = suc y} λ ()
  suc x =? zero  = no  {x = suc x} {y = zero}  λ ()
  suc x =? suc y = x =? y
  
  _≤?_ : ℕ → ℕ → Dec _≤_
  zero ≤? m = yes {y = m} z≤n 
  suc n ≤? suc m = n ≤? m
  suc n ≤? zero = no {x = suc n} {y = zero} λ ()  


-- определение стандартными средствами
-- module dec2 where

--   open import Relation.Nullary                      -- здесь определён тип Dec
--   open import Relation.Binary.PropositionalEquality using (cong)
  
--   _=?_ : (n m : ℕ) → Dec (n ≡ m)
--   zero  =? zero  = yes refl
--   zero  =? suc y = no  λ ()
--   suc n =? zero  = no  λ ()
--   suc n =? suc m with n =? m
--   ... | yes p = yes (cong suc p)
--   ... | no ¬p = no (¬p ∘ suc-injective)
--     where
--     suc-injective : ∀ {x y} → suc x ≡ suc y → x ≡ y
--     suc-injective refl = refl

--   _≤?_ : (n m : ℕ) → Dec (n ≤ m)
--   zero ≤? m = yes z≤n 
--   suc n ≤? zero = no λ ()  
--   suc n ≤? suc m with n ≤? m
--   ... | yes p = yes (s≤s p)
--   ... | no ¬p = no (¬p ∘ suc-injective)
--     where
--     suc-injective : ∀ {x y} → suc x ≤ suc y → x ≤ y
--     suc-injective (s≤s p) = p
  
