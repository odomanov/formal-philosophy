module TTCore where

open import Agda.Primitive public
open import Agda.Builtin.Bool public
open import Agda.Builtin.Equality public
open import Agda.Builtin.Sigma public renaming (fst to proj₁; snd to proj₂) hiding (module Σ)
module Σ = Agda.Builtin.Sigma.Σ renaming (fst to proj₁; snd to proj₂)
open import Agda.Builtin.Unit public

    
-- пустой тип
data ⊥ : Set where


-- Отрицание

infix 3 ¬_

¬_ : ∀ {a} → Set a → Set a 
¬ P = P → ⊥

infix 4 _≢_

_≢_ : ∀ {a} {A : Set a} → A → A → Set a 
x ≢ y = ¬ x ≡ y


-- ex falso quodlibet
⊥-elim : ∀ {a} {A : Set a} → ⊥ → A
⊥-elim ()

contradiction : ∀ {a} {A P : Set a} → P → ¬ P → A
contradiction p ¬p = ⊥-elim (¬p p)




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

