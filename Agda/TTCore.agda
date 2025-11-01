-- Ядро теории типов. Предназначено для использования в других файлах.
-- Отсутствует ℕ.

module TTCore where

open import Agda.Primitive public
open import Agda.Builtin.Equality public
open import Agda.Builtin.String public renaming (primStringEquality to _===_)

data Bool : Set where
  false true : Bool

record ⊤ : Set where
  instance constructor tt
-- data ⊤ : Set where
--   tt : ⊤
  
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

cong : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

subst : ∀ {a b} {A : Set a} {x y : A} (P : A → Set b) → x ≡ y → P x → P y
subst P refl p = p 

sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

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
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

-- принцип индукции
[_,_] : ∀ {a b c} {A : Set a} {B : Set b} {C : A ⊎ B → Set c}
        → ((x : A) → C (inj₁ x))
        → ((x : B) → C (inj₂ x)) 
        → ((x : A ⊎ B) → C x)
[ f , g ] (inj₁ x) = f x
[ f , g ] (inj₂ y) = g y



infixr 5 _∷_
data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

infixr 5 _++_
_++_ : ∀ {a} {A : Set a} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)


data Maybe {a} (A : Set a) : Set a where
  nothing : Maybe A
  just    : (x : A) → Maybe A



-- Вспомогательная функция inspect.
-- Скопировано из Relation.Binary.PropositionalEquality
record Reveal_·_is_ {a b} {A : Set a} {B : A → Set b}
                    (f : (x : A) → B x) (x : A) (y : B x) :
                    Set (a ⊔ b) where
  constructor [_]
  field eq : f x ≡ y

inspect : ∀ {a b} {A : Set a} {B : A → Set b}
          (f : (x : A) → B x) (x : A) → Reveal f · x is f x
inspect f x = [ refl ]



record Lift {a} ℓ (A : Set a) : Set (a ⊔ ℓ) where
  constructor lift
  field lower : A
