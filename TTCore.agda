-- Ядро теории типов. Предназначено для использования в других файлах.
-- Отсутствует ℕ.

module TTCore where

open import Agda.Primitive public
open import Agda.Builtin.Equality public
open import Agda.Builtin.String public renaming (primStringEquality to _==_)

data Bool : Set where
  false true : Bool

data ⊤ : Set where
  tt : ⊤
  
-- пустой тип
data ⊥ : Set where

-- Отрицание

infixr 3 ¬_

¬_ : ∀ {a} → Set a → Set a 
¬ P = P → ⊥


-- ex falso quodlibet
⊥-elim : ∀ {a} {A : Set a} → ⊥ → A
⊥-elim ()

contradiction : ∀ {a} {A P : Set a} → P → ¬ P → A
contradiction p ¬p = ⊥-elim (¬p p)


-- неравенство
infix 4 _≢_

_≢_ : ∀ {a} {A : Set a} → A → A → Set a 
x ≢ y = ¬ x ≡ y

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

infixr 4 _,_

infix 2 Σ-syntax

Σ-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B


infixr 4 _,′_
infixr 2 _×_

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ A (λ _ → B)

_,′_ : ∀ {a b} {A : Set a} {B : Set b} → A → B → A × B
_,′_ = _,_

proj₁′ : ∀ {a b} {A : Set a} {B : Set b} → A × B → A
proj₁′ = proj₁

proj₂′ : ∀ {a b} {A : Set a} {B : Set b} → A × B → B
proj₂′ = proj₂


-- Композиция функций

infixl 6 _∘_

_∘_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)


-- некоторые функции

id : ∀ {a} {A : Set a} → A → A
id x = x


const : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
const c _ = c


typeOf : ∀ {a} {A : Set a} → A → Set a
typeOf {A = A} _ = A


data _⊎_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B




infixr 5 _∷_
data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

infixr 5 _++_
_++_ : ∀ {a} {A : Set a} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)
