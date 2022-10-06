-- Структуры порядка.

module Order where

open import TTCore

-- Определения порядка
-- =================== 

-- Порядок (на типе, множестве) это бинарное отношение, удовлетворяющее
-- определённым условиям.
-- Минимальное условие -- транзитивность.


-- Виды порядка (и не только)
-- ========================== 

-- Отношение на A
Rel : Set → Set1
Rel A = A → A → Set 


record Equiv {A} (_≈_ : Rel A) : Set where
  field
    reflexivity  : ∀ x → x ≈ x
    transitivity : ∀ x y z → x ≈ y → y ≈ z → x ≈ z
    symmetry     : ∀ x y → x ≈ y → y ≈ x
    
    
record PreOrder {A} (_≤_ : Rel A) : Set where
  field
    reflexivity  : ∀ x → x ≤ x
    transitivity : ∀ x y z → x ≤ y → y ≤ z → x ≤ z
    
record PartialOrder {A} (_≈_ : Rel A) (_≤_ : Rel A) : Set where
  field
    reflexivity  : ∀ x → x ≤ x
    transitivity : ∀ x y z → x ≤ y → y ≤ z → x ≤ z
    antisymmetry : ∀ x y → x ≤ y → y ≤ x → x ≈ y
    
record PartialOrder' {A} (_≈_ : Rel A) (_≤_ : Rel A) : Set where
  field
    preorder     : PreOrder _≤_
    antisymmetry : ∀ x y → x ≤ y → y ≤ x → x ≈ y
  open PreOrder preorder
    
record TotalOrder {A} (_≈_ : Rel A) (_≤_ : Rel A) : Set where
  field
    po   : PartialOrder _≈_ _≤_ 
    univ : ∀ x y → (x ≤ y) ⊎ (y ≤ x)
  open PartialOrder po

record StrictOrder {A} (_<_ : Rel A) : Set where
  field
    irreflexivity : ∀ x → ¬ (x < x)
    transitivity  : ∀ x y z → x < y → y < z → x < z
    antisymmetry  : ∀ x y → x < y → ¬ (y < x) 
    


-- Аксиомы можно рассматривать как конструкторы

data _[≤]_ {A : Set} {_≤0_ : Rel A} : A → A → Set where
  init : ∀ x y → x ≤0 y → x [≤] y
  reflexivity : ∀ x → x [≤] x
  transitivity : ∀ x y z → _[≤]_ {A} {_≤0_} x y → _[≤]_ {A} {_≤0_} y z → x [≤] z
  symmetry : ∀ x y → _[≤]_ {A} {_≤0_} x y → y [≤] x


-- Операция на A
Op₂ : Set → Set
Op₂ A = A → A → A

Supremum : ∀ {A : Set} → Rel A → Op₂ A → Set
Supremum _≤_ _∨_ =
  ∀ x y → x ≤ (x ∨ y) × y ≤ (x ∨ y) × ∀ z → x ≤ z → y ≤ z → (x ∨ y) ≤ z

flip : ∀ {A : Set} → (A → A → Set) → A → A → Set
flip r x y = r y x

Infimum : ∀ {A : Set} → Rel A → Op₂ A → Set 
Infimum _≤_ = Supremum (flip _≤_)


-- Примеры порядков
-- ================ 

-- "Уровни знания" составляют частичный порядок.

-- TODO 

-- на числах
module Orgerℕ where
  open import Data.Nat using (ℕ; zero; suc)
  
  data _≤_ : ℕ → ℕ → Set where
    z≤n : ∀ {n}                 → zero  ≤ n
    s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n

  -- TODO: доказать свойства


-- на словах, лексикографический порядок
module OrgerWord where

  data Letter : Set where
    а б в г д : Letter

  -- порядок на буквах (должен быть полным!)
  data _≤L_ : Letter → Letter → Set where
    аа : а ≤L а
    бб : б ≤L б
    вв : в ≤L в
    гг : г ≤L г
    дд : д ≤L д
    аб : а ≤L б
    бв : б ≤L в
    вг : в ≤L г
    гд : г ≤L д
    trans : ∀ {x y z} → x ≤L y → y ≤L z → x ≤L z
    
  data Word : Set where
    ∅ : Word
    _∙_ : Letter → Word → Word

  infixr 5 _∙_
  
  data _≤_ : Word → Word → Set where
    ∅≤w : ∀ {w} → ∅ ≤ w
    ∙w  : ∀ {x y xs ys} → (x ≤L y) → (x ∙ xs) ≤ (y ∙ ys) 

  _ : (а ∙ б ∙ ∅) ≤ (б ∙ ∅)
  _ = ∙w аб

  _ : (а ∙ б ∙ ∅) ≤ (а ∙ г ∙ ∅)
  _ = ∙w аа

  _ : (б ∙ ∅) ≤ (б ∙ а ∙ ∅)
  _ = ∙w бб

  _ : (а ∙ ∅) ≤ (в ∙ ∅)
  _ = ∙w (trans аб бв)

  -- Свойства

  OWreflexivity : ∀ x → x ≤ x
  OWreflexivity ∅ = ∅≤w
  OWreflexivity (а ∙ x₁) = ∙w аа
  OWreflexivity (б ∙ x₁) = ∙w бб
  OWreflexivity (в ∙ x₁) = ∙w вв
  OWreflexivity (г ∙ x₁) = ∙w гг
  OWreflexivity (д ∙ x₁) = ∙w дд

  OWtransitivity : ∀ x y z → x ≤ y → y ≤ z → x ≤ z
  OWtransitivity x y z xy yz = {!!}

  OWantisymmetry : ∀ x y → x ≤ y → y ≤ x → x ≡ y
  OWantisymmetry x y xy yx = {!!}
