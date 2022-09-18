module Ralph where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)


data НосительМнения : Set where   -- or Perspective
  Ральф Мы : НосительМнения
  
open import Monad.Identity
open import Monad.Reader   

IntMonad = MonadReader НосительМнения

-- intensional
∧ : ∀ {ℓ} → Set ℓ → Set ℓ
∧ = Reader НосительМнения

-- wrap a function from Мир into the intensional type
mkIntensional : ∀ {a} {A : Set a} → (НосительМнения → A) → ∧ A
mkIntensional f = mkReaderT (λ w → mkIdentity (f w))

-- extensional
∨ : ∀ {ℓ} {A : Set ℓ} → ∧ A → (НосительМнения → A)
∨ = runReader                 

rigid = return

infixl 5 _★_
_★_ = _>>=_




data Человек : Set where
  чел-в-шляпе чел-на-пляже Орткут : Человек

postulate
  spy : Человек → Set

xh : ∧ Человек
xh = mkIntensional f
  where
  f : НосительМнения → Человек
  f Ральф = чел-в-шляпе
  f Мы = Орткут

xb : ∧ Человек
xb = mkIntensional f
  where
  f : НосительМнения → Человек
  f Ральф = чел-на-пляже
  f Мы = Орткут

postulate
  _считает-что_шпион : НосительМнения → Человек → Set
  spyh : Ральф считает-что чел-в-шляпе шпион
  spyb : Ральф считает-что чел-на-пляже шпион → ⊥

_считаем-что_шпион = _считает-что_шпион

iСчитает-шпионом : Человек → (∧ Set)
iСчитает-шпионом h = mkIntensional (λ b → b считает-что h шпион)


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


-- ⊸   \ -o


-- -- believes that spy
-- BelSpy : Человек → (НосительМнения → Set)
-- -- BelSpy h = ∨ (iСчитает-шпионом h)    -- BelSpy = ipsy ?
-- BelSpy h b = h spy/ b 

-- _ : (xh ★ BelSpy) Ральф 
-- _ = spyh

-- postulate
--   believe : (A : Set) → (∧ Set)

-- -- BelSpy' : Человек → (НосительМнения → Set)
-- -- BelSpy' h b = believe Человек (iСчитает-шпионом h) 
