module Ralph where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)


data НосительМнения : Set where   -- or Perspective
  Ральф Мы : НосительМнения
  
open import Intensional НосительМнения

∧ = Intensional

-- extensional
∨ : ∀ {ℓ} {A : Set ℓ} → ∧ A → (НосительМнения → A)
∨ = getFunction                 

rigid = return

infixl 5 _★_
_★_ = _>>=_



data Человек : Set where
  чел-в-шляпе чел-на-пляже Орткут : Человек

postulate
  spy : Человек → Set

xh : ∧ Человек
xh Ральф = чел-в-шляпе
xh Мы = Орткут

xb : ∧ Человек
xb Ральф = чел-на-пляже
xb Мы = Орткут

postulate
  _считает-что_шпион : НосительМнения → Человек → Set
  spyh : Ральф считает-что чел-в-шляпе шпион
  spyb : Ральф считает-что чел-на-пляже шпион → ⊥

_считаем-что_шпион = _считает-что_шпион

iСчитает-шпионом : Человек → (∧ Set)
iСчитает-шпионом h = λ b → b считает-что h шпион


⟦_⟧/_ : ∀ {i} {A : Set i} → ∧ A → НосительМнения → A
⟦ ma ⟧/ b = ∨ ma b

_ : ⟦ xh ★ iСчитает-шпионом ⟧/ Ральф ≡ Ральф считает-что чел-в-шляпе шпион
_ = refl

_ : ⟦ xh ★ iСчитает-шпионом ⟧/ Ральф
_ = spyh

_ : ⟦ xb ★ iСчитает-шпионом ⟧/ Ральф → ⊥
_ = spyb

_ : ⟦ rigid Орткут ★ iСчитает-шпионом ⟧/ Мы ≡ Мы считаем-что Орткут шпион
_ = refl

_ : ⟦ rigid Орткут ★ iСчитает-шпионом ⟧/ Ральф ≡ Ральф считает-что Орткут шпион
_ = refl

-- невозможно доказать
_ : ⟦ rigid Орткут ★ iСчитает-шпионом ⟧/ Ральф
_ = {!!}


