module TTCore where

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma public renaming (fst to proj₁; snd to proj₂) hiding (module Σ)
module Σ = Agda.Builtin.Sigma.Σ renaming (fst to proj₁; snd to proj₂)
open import Agda.Builtin.Unit

    
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


_×_ : ∀ {ℓ} (A B : Set ℓ) → Set ℓ 
A × B = Σ A (λ _ → B)




-- Композиция функций

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)


-- некоторые функции

id : ∀ {A : Set} → A → A
id x = x


const : ∀ {A B : Set} → A → B → A
const c _ = c


typeOf : ∀ {A} → A → Set
typeOf {A} _ = A

