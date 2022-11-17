-- Структуры порядка.
-- Файл демонстрирует определения алгебраических структур с помощью record.

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


-- Предпорядок
record PreOrder {A} (_≤_ : Rel A) : Set where
  field
    reflexivity  : ∀ x → x ≤ x
    transitivity : ∀ x y z → x ≤ y → y ≤ z → x ≤ z

-- Частичный порядок
record PartialOrder {A} (_≈_ : Rel A) (_≤_ : Rel A) : Set where
  field
    reflexivity  : ∀ x → x ≤ x
    transitivity : ∀ x y z → x ≤ y → y ≤ z → x ≤ z
    antisymmetry : ∀ x y → x ≤ y → y ≤ x → x ≈ y

-- Ещё раз частичный порядок
record PartialOrder' {A} (_≈_ : Rel A) (_≤_ : Rel A) : Set where
  field
    preorder     : PreOrder _≤_
    antisymmetry : ∀ x y → x ≤ y → y ≤ x → x ≈ y
  open PreOrder preorder

-- Полный порядок
record TotalOrder {A} (_≈_ : Rel A) (_≤_ : Rel A) : Set where
  field
    po   : PartialOrder _≈_ _≤_ 
    univ : ∀ x y → (x ≤ y) ⊎ (y ≤ x)
  open PartialOrder po

-- Строгий порядок
record StrictOrder {A} (_<_ : Rel A) : Set where
  field
    irreflexivity : ∀ x → ¬ (x < x)
    transitivity  : ∀ x y z → x < y → y < z → x < z
    antisymmetry  : ∀ x y → x < y → ¬ (y < x) 
    

-- Эквивалентность 
record Equiv {A} (_≈_ : Rel A) : Set where
  field
    reflexivity  : ∀ x → x ≈ x
    transitivity : ∀ x y z → x ≈ y → y ≈ z → x ≈ z
    symmetry     : ∀ x y → x ≈ y → y ≈ x
    
    

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

---------------------------------------------------------------------------------
-- "Уровни знания" составляют частичный порядок.

-- TODO 



---------------------------------------------------------------------------------
-- на числах
module Orderℕ where
  open import Nat using (ℕ; zero; suc)
  
  data _≤_ : ℕ → ℕ → Set where
    z≤n : ∀ {n}                 → zero  ≤ n
    s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n

  -- TODO: доказать свойства
  reflex : ∀ x → x ≤ x
  reflex x = {!!}
  
  asym : ∀ x y → x ≤ y → y ≤ x → x ≡ y
  asym x y xy yx = {!!}
  
  trans : ∀ x y z → x ≤ y → y ≤ z → x ≤ z
  trans x y z xy yz = {!!}

  -- определение частичного порядка
  POℕ : PartialOrder _≡_ _≤_
  POℕ = record { reflexivity = reflex
               ; antisymmetry = asym
               ; transitivity = trans
               }


---------------------------------------------------------------------------------
-- на словах, лексикографический порядок
module OrderWord where

  data Letter : Set where
    а б в г : Letter

  -- порядок на буквах (должен быть строгим!)
  data _<L_ : Letter → Letter → Set where
    аб : а <L б
    ав : а <L в
    аг : а <L г
    бв : б <L в
    бг : б <L г
    вг : в <L г

  irreflex : ∀ {x} → ¬ x <L x
  irreflex ()
    
  trans  : ∀ {x y z} → x <L y → y <L z → x <L z
  trans аб бв = ав
  trans аб бг = аг
  trans ав вг = аг
  trans бв вг = бг

  asym : ∀ {x y} → x <L y → ¬ y <L x 
  asym аб ()
  asym ав ()
  asym аг ()
  asym бв ()
  asym бг ()
  asym вг ()

    
  data Word : Set where
    ∅ : Word
    _∙_ : Letter → Word → Word

  infixr 5 _∙_

  -- Порядок на словах
  data _<_ : Word → Word → Set where
    ∅<w : ∀ {w} → ¬ w ≡ ∅ → ∅ < w
    <w  : ∀ {x y xs ys} → (x <L y) → (x ∙ xs) < (y ∙ ys)
    =w  : ∀ {x y xs ys} → x ≡ y → xs < ys → (x ∙ xs) < (y ∙ ys)

  _ : (а ∙ б ∙ ∅) < (б ∙ ∅)
  _ = <w аб

  _ : (а ∙ б ∙ ∅) < (а ∙ г ∙ ∅)
  _ = =w refl (<w бг)

  _ : (б ∙ ∅) < (б ∙ а ∙ ∅)
  _ = =w refl (∅<w (λ ())) 

  _ : (а ∙ ∅) < (в ∙ ∅)
  _ = <w (trans аб бв)

  -- Свойства

  OWirreflexivity : ∀ x → ¬ x < x
  OWirreflexivity ∅ (∅<w ¬∅≡∅) = ¬∅≡∅ refl
  OWirreflexivity (_ ∙ xs) (=w refl p) = OWirreflexivity xs p

  ≡sym : ∀ {x y : Letter} → x ≡ y → y ≡ x
  ≡sym refl = refl

  ≡trans : ∀ {x y z : Letter} → x ≡ y → y ≡ z → x ≡ z
  ≡trans refl refl = refl
  
  OWtransitivity : ∀ x y z → x < y → y < z → x < z
  OWtransitivity ∅ ∅ _ _ yz = yz
  OWtransitivity ∅ (x ∙ y) (x₁ ∙ z) xy yz = ∅<w (λ ())
  OWtransitivity (x ∙ xs) (y ∙ ys) (z ∙ zs) (<w xy) (<w yz) =
    <w (trans {y = y} xy yz)
  OWtransitivity (x ∙ xs) (y ∙ ys) (z ∙ zs) (<w xy) (=w y≡z yz) =
    <w (subst _ y≡z xy)
  OWtransitivity (x ∙ xs) (y ∙ ys) (z ∙ zs) (=w x≡y xy) (<w yz) =
    <w (subst _ (≡sym x≡y) yz)
  OWtransitivity (x ∙ xs) (y ∙ ys) (z ∙ zs) (=w x≡y xy) (=w y≡z yz) =
    =w (≡trans x≡y y≡z) (OWtransitivity _ ys _ xy yz)

  OWantisymmetry : ∀ {x y} → x < y → ¬ y < x 
  OWantisymmetry (∅<w _) (∅<w p) = p refl
  OWantisymmetry (<w xy) (<w yx) = asym xy yx
  OWantisymmetry (<w ав) (=w () yx)
  OWantisymmetry (<w бв) (=w () yx)
  OWantisymmetry (<w бг) (=w () yx)
  OWantisymmetry (<w вг) (=w () yx)
  OWantisymmetry (=w () xy) (<w аб)
  OWantisymmetry (=w () xy) (<w ав)
  OWantisymmetry (=w () xy) (<w аг)
  OWantisymmetry (=w () xy) (<w бв)
  OWantisymmetry (=w () xy) (<w бг)
  OWantisymmetry (=w () xy) (<w вг)
  OWantisymmetry (=w x≡y xy) (=w y≡x yx) = OWantisymmetry xy yx


  -- определение строгого порядка
  OW : StrictOrder _<_
  OW = record { irreflexivity = OWirreflexivity
              ; transitivity = OWtransitivity
              ; antisymmetry = λ x y → OWantisymmetry {x} {y}
              }
