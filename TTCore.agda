module TTCore where

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
    
-- пустой тип
data ⊥ : Set where

-- всегда истинный тип
data ⊤ : Set where
  tt : ⊤


-- ex falso quodlibet
⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()


-- Отрицание
infix 3 ¬_

¬_ : Set → Set 
¬ P = P → ⊥

infix 4 _≢_

_≢_ : {A : Set} → A → A → Set 
x ≢ y = ¬ x ≡ y

contradiction : ∀ {A : Set} {P : A → Set} {x : A} → P x → ¬ P x → A
contradiction p ¬p = ⊥-elim (¬p p)


module m1 where
  open import Agda.Builtin.Nat

  0≢1 : ¬ zero ≡ suc zero    -- zero ≡ suc zero → ⊥
  0≢1 () 
  
  0≢suc : ∀ {n} → ¬ zero ≡ suc n
  0≢suc ()

  a : ¬ zero ≢ zero       -- (zero ≡ zero → ⊥) → ⊥
  a p = p refl 




-- Σ-тип
-- =====

data Sigma (A : Set) (B : A → Set) : Set1 where
  _,_ : (x : A) → (y : B x) → Sigma A B

pr₁ : ∀ {A} {B : A → Set} → Sigma A B → A
pr₁ (x , _) = x

pr₂ : ∀ {A} {B : A → Set} → (s : Sigma A B) → B (pr₁ s)
pr₂ (_ , y) = y

infixr 4 _,_


-- Теорема (требует равенства для универсума Set₁)

-- T1 = ∀ {A} {B : A → Set} (s : Sigma A B) → (s ≡ (proj₁ s , proj₂ s))

-- prf1 : T1
-- prf1 (x , y) = refl


-- Как определено в стандартной библиотеке (почти):

module Σ where

  -- кортеж
  record Σ (A : Set) (B : A → Set) : Set1 where
    constructor _,_
    field
      proj₁ : A
      proj₂ : B proj₁

  -- record -- тип с одним конструктором.
  -- Ср. определение Sigma.
  

_×_ : (A B : Set) → Set1
A × B = Sigma A (λ _ → B)


∃ : {A : Set} → (A → Set) → Set1
∃ B = Sigma _ B                      -- существует A, такое, что B 


-- Пример

module ex1 where

  data Страна : Set where
    Япония Буркина-Фасо : Страна

  data Город : Страна → Set where
    Токио        : Город Япония
    Саппоро      : Город Япония
    Уагадугу     : Город Буркина-Фасо
    Бобо-Диуласо : Город Буркина-Фасо
  
  _ : ∃ Город                   -- существует страна, такая, что в ней есть город
  _ = Япония , Токио

  _ : ∃ Город
  _ = Буркина-Фасо , Уагадугу

  -- Это пропозиция "существует страна"
  _ : Страна
  _ = Япония


  Страна' : ⊤ → Set
  Страна' tt = Страна
  
  _ : ∃ {⊤} Страна'
  _ = tt , Япония


  _ : ∃ {⊤} (λ _ → Страна)
  _ = tt , Япония

  _ : Sigma ⊤ (λ _ → Страна)
  _ = tt , Буркина-Фасо

  ∃' : Set → Set1
  ∃' B = Sigma ⊤ (λ _ → B)

  _ : ∃' Страна
  _ = tt , Япония





-- Каррирование

curry : ∀ {A : Set} {B : A → Set} {C : Sigma A B → Set} 
        → ((p : Sigma A B) → C p) 
        → ((x : A)
        → (y : B x)
        → C (x , y))
curry f x y = f (x , y)

uncurry : ∀ {A : Set} {B : A → Set} {C : Sigma A B → Set} 
          → ((x : A) → (y : B x) → C (x , y)) 
          → ((p : Sigma A B) → C p)
uncurry f (x , y) = f x y


-- для независимых типов

curry′ : ∀ {A B C} → (A × B → C) → (A → B → C)
curry′ = curry

uncurry′ : ∀ {A B C} → (A → B → C) → (A × B → C)
uncurry′ = uncurry




-- Тип функций
-- ===========

-- Относится к базовым.

_=>_ : (A B : Set) → Set
A => B = (_ : A) → B
-- A => B = A → B


-- Композиция функций

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)

