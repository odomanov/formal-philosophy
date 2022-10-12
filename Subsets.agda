-- Подмножества множества E

module Subsets (E : Set) where

open import TTCore hiding ([_]) 

-- type of subsets
Subset : Set₁
Subset = E → Set

-- принадлежность
_∈_ : E → Subset → Set
e ∈ A = A e

-- объединение
_∪_ : Subset → Subset → Subset
A ∪ B = λ e → A e ⊎ B e

-- пересечение
_∩_ : Subset → Subset → Subset
A ∩ B = λ e → A e × B e

-- дополнение (до E)
∁ : Subset → Subset
∁ A = λ e → (A e → ⊥)

-- A -- подмножество B
_⊆_ : Subset → Subset → Set
A ⊆ B = (e : E) → A e → B e

-- равенство
_≈_ : Subset → Subset → Set
A ≈ B = A ⊆ B × B ⊆ A

-- Всё множество (универсум)
U : Subset
U = λ e → ⊤

-- U не равно E, но можно попробовать доказать их эквивалентность.

_ : ∀ (e : E) → e ∈ U
_ = λ e → tt

-- Обратная импликация выполняется автоматически, но доказать это в нашем
-- формализме нельзя!  Нельзя даже сформулировать.


-- пустое множество
∅ : Subset
∅ = λ e → ⊥

-- разность множеств
_-_ : Subset → Subset → Subset
A - B = A ∩ ∁ B

-- Множество-степень.
-- 𝒫 не может быть Subset, т.к. принадлежит Set₂
𝒫 : Set₂
𝒫 = (E → Set) → Set₁

infix 1 _≈_
infix 3 _⊆_
infix 4 _-_


-- Вспомогательная функция
-- id : {A : Set} → A → A
-- id x = x


-- Некоторые теоремы

A-∅=A : ∀ {A} → A - ∅ ≈ A
A-∅=A = (λ e → proj₁) , (λ e x → x , id)

U-A=∁A : ∀ {A} → U - A ≈ ∁ A
U-A=∁A = (λ e → proj₂) , (λ e → tt ,_) 

A∪∁A⊆U : ∀ {A} → A ∪ ∁ A ⊆ U
A∪∁A⊆U _ _ = tt

-- обратное нельзя доказать в интуиционизме
-- но можно в классике

-- Закон исключённого третьего.
LEM = ∀ {s : Set} → s ⊎ (s → ⊥)

¬¬ : ∀ {s : Set} → LEM → ((s → ⊥) → ⊥) → s
¬¬ {s} lem x = [ id , g x ] lem                  -- [ id , g x ]′ = ⊎-induction
  where
  g : ∀ {s} → ((s → ⊥) → ⊥) → (s → ⊥) → s
  g x y = ⊥-elim (x y) 

-- теперь докажем в предположении LEM

U⊆A∪∁A/LEM : ∀ {A} → LEM → U ⊆ A ∪ ∁ A
U⊆A∪∁A/LEM lem _ _ = lem

A∪∁A=U/LEM : ∀ {A} → LEM → (A ∪ ∁ A) ≈ U
A∪∁A=U/LEM lem = A∪∁A⊆U , U⊆A∪∁A/LEM lem 


A⊆∁∁A : ∀ {A} → A ⊆ ∁ (∁ A)
A⊆∁∁A e x y = y x 

∁∁A⊆A/LEM : ∀ {A} → LEM → ∁ (∁ A) ⊆ A
∁∁A⊆A/LEM lem e x = ¬¬ lem x

∁∁A=A : ∀ {A} → LEM → ∁ (∁ A) ≈ A
∁∁A=A {A} lem = (λ e x → ∁∁A⊆A/LEM {A} lem e x) , (λ e x y → A⊆∁∁A {A} e x y)


A⊆U-∁A : ∀ {A} → A ⊆ U - ∁ A
A⊆U-∁A e z = tt , (λ x → x z)

U-∁A⊆A/LEM : ∀ {A} → LEM → U - ∁ A ⊆ A
U-∁A⊆A/LEM {A} lem e (tt , snd) = ¬¬ lem snd

U-∁A=A/LEM : ∀ {A} → LEM → U - ∁ A ≈ A
U-∁A=A/LEM lem = U-∁A⊆A/LEM lem , A⊆U-∁A


A∩∁A=∅ : ∀ {A} → (A ∩ ∁ A) ≈ ∅
A∩∁A=∅ = (λ e z → proj₂ z (proj₁ z)) , λ e () 

A∩B⊆A : ∀ {A B} → (A ∩ B) ⊆ A
A∩B⊆A e = proj₁

A⊆A∪B : ∀ {A B} → A ⊆ (A ∪ B)
A⊆A∪B e = inj₁
