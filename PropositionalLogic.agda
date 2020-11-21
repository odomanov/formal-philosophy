{-# OPTIONS --prop #-}

module PropositionalLogic where

open import Agda.Builtin.Equality


module Boolean where

  data TruthValue : Set where
    true  : TruthValue
    false : TruthValue
    
  data Atom : Set where
    P Q R : Atom
  
  data Val : Set where
    val : Atom → TruthValue → Val  
  
  
  _∧_ : Val → Val → TruthValue
  (val _ true) ∧ (val _ true) = true
  _ ∧ _ = false
  
  _∨_ : Val → Val → TruthValue
  (val _ false) ∨ (val _ false) = false
  _ ∨ _ = true
  
  ¬ : Val → TruthValue
  ¬ (val _ true) = false
  ¬ (val _ false) = true
  
  
  vP : Val 
  vP = val P true
  
  vQ : Val 
  vQ = val Q true
  
  vR : Val 
  vR = val R false
  
  
  _ : vP ∧ vQ ≡ true
  _ = refl
  
  _ : vQ ∨ vR ≡ true
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
  
  fst : ∀ {A B} → some A are B → A
  fst (a is _) = a

  snd : ∀ {A B} → some A are B → B
  snd (_ is b) = b


  Barbara : ∀ {A B C} → all A are B → all B are C → all A are C
  Barbara f g = λ x → g (f x)


  Darii : ∀ {A B C : Set} → all A are B → some C are A → some C are B     
  Darii f x = (fst x) is (f (snd x))


  Celarent : ∀ {A B C} → no A are B → all C are A → no C are B
  Celarent f g = λ x → f ((g (fst x)) is (snd x))
