-- Логика первого порядка

module FOL where


-- Интуиционистская логика
-- =======================

module Int where

  data ⊥ : Set where

  data ⊤ : Set where
    tt : ⊤

  data _∧_ (A B : Set) : Set where
    _,_ : A → B → A ∧ B

  data _∨_ (A B : Set) : Set where
    inl : A → A ∨ B
    inr : B → A ∨ B

  ¬ : Set → Set
  ¬ A = A → ⊥

  postulate D : Set        -- предполагаем домен

  -- встроено в Агду
  ∀' : (D → Set) → Set
  ∀' P = ∀ (x : D) → P x

  syntax ∀' (λ x → P) = ∀[ x ] P


  data ∃ (P : D → Set) : Set where
    _,_ : (x : D) → P x → ∃ P 

  syntax ∃ (λ x → P) = ∃[ x ] P


  -- Чуть более сложные определения.
  -- Без предположения домена.

  ∀'' : (A : Set) → (A → Set) → Set
  ∀'' A P = (x : A) → P x

  syntax ∀'' A (λ x → P) = ∀[ x ∈ A ] P

  data ∃' (A : Set) (P : A → Set) : Set where
    _,_ : (x : A) → P x → ∃' A P

  syntax ∃' A (λ x → P) = ∃[ x ∈ A ] P




-- Неинтуиционистская логика
-- =========================

module NonInt where

  open import Agda.Builtin.Equality

  data Bool : Set where
    true  : Bool
    false : Bool

  _∧_ : Bool → Bool → Bool
  true ∧ true = true
  _ ∧ _ = false

  _∨_ : Bool → Bool → Bool
  false ∨ false = false
  _ ∨ _ = true

  ¬ : Bool → Bool
  ¬ true = false
  ¬ false = true


  open import Agda.Builtin.List

  postulate
    O : Set             -- тип объектов
    D : List O          -- чтобы можно было пробегать по домену

  -- Вспомогательная функция
  fold : ∀ {A B : Set} → (A → B) → B → (B → B → B) → List A → B
  fold _ b _ [] = b
  fold P b o (x ∷ xs) = o (P x) (fold P b o xs)

  ∀' : (O → Bool) → Bool
  ∀' P = fold P true _∧_ D
  -- ∀' P = foldr true _∧_ (map P D)

  ∃ : (O → Bool) → Bool
  ∃ P = fold P false _∨_ D
  -- ∃ P = foldr false _∨_ (map P D)

  syntax ∀' (λ x → P) = ∀[ x ] P
  syntax ∃  (λ x → P) = ∃[ x ] P


  -- Вместо Bool можно использовать ⊥, ⊤.
  -- Т.е. Bool это два типа пропозиций.


-- Здесь везде предполагается, что у нас есть домен, т.е. модель!
