-- Montague semantics in terms of TT

open import Agda.Primitive
open import TTCore

module _ where

-- Части речи. Общая интерпретация
-- ===============================

VP : ∀ {ℓ} → Set ℓ → Set (lsuc ℓ)
VP {ℓ} A = A → Set ℓ 

NP : ∀ {ℓ} → Set ℓ → Set (lsuc ℓ)
NP {ℓ} A = (A → Set ℓ) → Set ℓ

CN : ∀ {ℓ} → Set ℓ → Set ℓ
CN A = A

DET : ∀ {ℓ} → Set (lsuc ℓ) 
DET {ℓ} = (A : Set ℓ) → (A → Set ℓ) → Set ℓ 

AP : ∀ {ℓ} → Set ℓ → Set (lsuc ℓ)
AP {ℓ} A = A → Set ℓ

VI : ∀ {ℓ} (A : Set ℓ) → Set (lsuc ℓ)
VI {ℓ} A = A → Set ℓ


-- Семантика
-- =========

postulate
  *Human : Set
  *Alex *Mary : *Human
  *runs : VI *Human

vp-v : ∀ {ℓ} {A : Set ℓ} → VI A → VP A
vp-v {A = A} v x = v x

runs : VP *Human
runs = vp-v *runs

np-pn : ∀ {ℓ} {A : Set ℓ} → A → NP A
np-pn pn v = v pn

Mary : NP *Human           -- Mary as a noun phrase
Mary = np-pn *Mary


s1 = Mary runs

s2 = (np-pn *Mary) runs



postulate
  *Dog : Set
  *Polkan : *Dog

Polkan : NP *Dog
Polkan = np-pn *Polkan


-- s3 = Polkan runs     -- это не работает! нужна коэрсия



--  Определители (артикли и пр.)

a : ∀ {ℓ} → DET {ℓ}
a A v = Σ A v 

every : ∀ {ℓ} → DET {ℓ}
every A v = (x : A) → v x

no : ∀ {ℓ} → DET {ℓ}
no A v = (x : A) → ¬ v x

-- the : ∀ {ℓ} {A : Set ℓ} → A → DET {ℓ}
-- the a = λ A v → v {!!}


a-human : NP *Human
a-human = a *Human

s4 = a-human runs


every-human : NP *Human
every-human = every *Human

s5 = every-human runs    


-- Другой способ

Human = CN *Human

_ : Human ≡ *Human
_ = refl

s6 = (a Human) runs  

s7 = (every Human) runs  

s8 = (no Human) runs




-- Прилагательные / свойства

postulate
  *big : *Dog → Set
  *polkan-is-big : *big *Polkan

ap-a : ∀ {ℓ} {A : Set ℓ} → (A → Set ℓ) → AP A
ap-a x = x

big : AP *Dog
big = ap-a *big


cn-ap : ∀ {ℓ} {A : Set ℓ} {ap : AP A} → (x : A) → (ap x) → CN (Σ A ap)
cn-ap x px = x , px

big-dog : CN (Σ *Dog big)
big-dog = cn-ap *Polkan *polkan-is-big


-- cn-ap корректно:

_ : ∀ {ℓ} {A : Set ℓ} {ap : AP A} (x : A) → ap x → CN (Σ A ap)
_ = λ x px → cn-ap x px





-- Относительные конструкции (CN that VP и пр.)

RCN : ∀ {ℓ} (A : Set ℓ) → VP A → Set _
RCN A vp = CN (Σ A vp)

rcn : ∀ {ℓ} {A : Set ℓ} {vp : VP A} → (x : A) → vp x → RCN A vp 
rcn x vx = x , vx


postulate
  *Mary-runs : *runs *Mary

Mary-that-runs : RCN *Human *runs
Mary-that-runs = rcn *Mary *Mary-runs

a-human-that-runs : NP (Σ *Human *runs)
a-human-that-runs = a (RCN *Human *runs)


--s9 = a-human-that-runs runs   -- не работает!  нужна коэрсия


postulate
  *sings : Σ *Human *runs → Set

sings = vp-v *sings

s10 = a-human-that-runs sings




