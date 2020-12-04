{-# OPTIONS --prop #-}

module PropositionalLogic where

open import Agda.Builtin.Equality


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






-- Моделирование пропозициональной логики
-- ======================================

module B where

  data Bool : Set where
    true  : Bool
    false : Bool
    
  data Atom : Set where
    P Q R : Atom

  -- Оценка атомов
  val : Atom → Bool
  val P = true
  val Q = false
  val R = true

  -- Операции на Bool
  _AND_ : Bool → Bool → Bool
  true AND true = true
  _ AND _ = false

  _OR_ : Bool → Bool → Bool
  false OR false = false
  _ OR _ = true

  NOT : Bool → Bool
  NOT true = false
  NOT false = true


  -- Выражения пропозициональной логики
  data Exp : Set where
    `   : Atom → Exp
    _∧_ : Exp  → Exp → Exp
    _∨_ : Exp  → Exp → Exp
    ¬_  : Exp  → Exp

  _=>_ : Exp → Exp → Exp
  A => B = ¬ A ∨ B

  eval : Exp → Bool
  eval (` p)   = val p
  eval (p ∧ q) = (eval p) AND (eval q)
  eval (p ∨ q) = (eval p) OR (eval q)
  eval (¬ p)   = NOT (eval p)


  infix 5 _∧_ _∨_
  infix 6 ¬_

  _ : eval (` P ∧ ` Q) ≡ false
  _ = refl

  _ : eval (` P ∧ (¬ ` Q ∨ ` R)) ≡ true
  _ = refl
  





-- Тип Prop
-- ========

module PropType where
  open import Agda.Builtin.Nat

  -- Тип ложных пропозиций.
  data ⊥ : Prop where

  -- Тип истинных пропозиций.
  data ⊤ : Prop where
    tt : ⊤


  _is-even : Nat → Prop 
  zero is-even = ⊤
  (suc (suc n)) is-even = n is-even
  _ is-even = ⊥
  
  -- Определить is-even как тип сложно, т.к. все его конструкторы должны совпадать.



  
-- Силлогизмы
-- ==========


module Syllogism where

  -- Утвердительные суждения

  -- AaB
  all_are_ : ∀ (A B : Set) → Set
  all A are B = A → B

  -- AiB
  -- В силлогистике объекты могут принадлежать нескольким типам.
  data some_are_ (A : Set) (B : Set) : Set where 
    _is_ : A → B → some A are B

  -- Отрицательные суждения

  data ⊥ : Set where

  ¬ : Set → Set 
  ¬ A = A → ⊥ 

  -- AeB
  no_are_ : ∀ (A : Set) (B : Set) → Set 
  no A are B = (some A are B) → ⊥ 

  -- AoB
  some_are-not_ : ∀ (A : Set) (B : Set) → Set 
  some A are-not B = some A are (B → ⊥)



  -- некоторые силлогизмы
  

  Barbara : ∀ {A B C} → all A are B → all B are C → all A are C
  Barbara f g = λ x → g (f x)


  -- Вспомогательные функции
  fst : ∀ {A B} → some A are B → A
  fst (a is _) = a

  snd : ∀ {A B} → some A are B → B
  snd (_ is b) = b


  Darii : ∀ {A B C : Set} → all A are B → some C are A → some C are B     
  Darii f x = (fst x) is (f (snd x))


  Celarent : ∀ {A B C} → no A are B → all C are A → no C are B
  Celarent f g = λ x → f ((g (fst x)) is (snd x))
