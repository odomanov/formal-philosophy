module TTCoreSimple where

infix 4 _≡_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
    
-- пустой тип
data ⊥ : Set where

-- всегда истинный тип
data ⊤ : Set where
  tt : ⊤



-- Отрицание

infix 3 ¬_

¬_ : Set → Set 
¬ P = P → ⊥

infix 4 _≢_

_≢_ : {A : Set} → A → A → Set 
x ≢ y = ¬ x ≡ y


-- ex falso quodlibet
⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

contradiction : ∀ {A P : Set} → P → ¬ P → A
contradiction p ¬p = ⊥-elim (¬p p)

contraposition : ∀ {P Q : Set} → (P → Q) → ¬ Q → ¬ P
contraposition f ¬q p = contradiction (f p) ¬q


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

-- кортеж
record Σ (A : Set) (B : A → Set) : Set1 where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

-- record -- тип с одним конструктором.
-- Ср. определение Sigma.
  

_×_ : (A B : Set) → Set1
A × B = Σ A (λ _ → B)

_,′_ : ∀ {A B : Set} → A → B → A × B
_,′_ = _,_




-- В библиотеке определено также: Σ[ x ∈ A ] B
-- Это равно Σ A (λ x → B).



-- Пример

module ex1 where

  data Страна : Set where
    Япония Буркина-Фасо : Страна

  data Город : Страна → Set where
    Токио        : Город Япония
    Саппоро      : Город Япония
    Уагадугу     : Город Буркина-Фасо
    Бобо-Диуласо : Город Буркина-Фасо
  
  _ : Σ _ Город                   -- существует страна, такая, что в ней есть город
  _ = Япония , Токио

  _ : Σ _ Город
  _ = Буркина-Фасо , Уагадугу


  -- Это пропозиция "существует страна"
  _ : Страна
  _ = Япония

  _ : Σ Страна (λ _ → ⊤)
  _ = Япония , tt


  Страна' : ⊤ → Set
  Страна' tt = Страна
  
  _ : Σ ⊤ Страна'
  _ = tt , Япония

  _ : Σ ⊤ (λ _ → Страна)
  _ = tt , Буркина-Фасо






-- Каррирование

curry : ∀ {A : Set} {B : A → Set} {C : Σ A B → Set} 
        → ((p : Σ A B) → C p) 
        → ((x : A)
        → (y : B x)
        → C (x , y))
curry f x y = f (x , y)

-- Σ-elim
uncurry : ∀ {A : Set} {B : A → Set} {C : Σ A B → Set} 
          → ((x : A) → (y : B x) → C (x , y)) 
          → ((p : Σ A B) → C p)
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
A => B = A → B


-- Композиция функций

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)


-- некоторые функции

id : ∀ {A : Set} → A → A
id x = x


const : ∀ {A B : Set} → A → B → A
const c _ = c

_ : ∀ {A B} {c : A} → const c ≡ λ (_ : B) → c
_ = refl



typeOf : ∀ {A} → A → Set
typeOf {A} _ = A



data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B
