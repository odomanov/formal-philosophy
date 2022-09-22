-- Силлогизмы

module _ where

-- В предикатной логике A,E,I,O это ограниченные кванторы!

module Syllogism where

  -- Утвердительные суждения

  -- AaB
  all_are_ : ∀ (A B : Set) → Set
  all A are B = A → B

  -- AiB
  -- В силлогистике объекты могут принадлежать нескольким типам.
  data some_are_ (A : Set) (B : Set) : Set where 
    _is_ : A → B → some A are B                     -- ср. с Σ или A × B

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
