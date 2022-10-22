-- Montague semantics in terms of TT

open import TTCore

module _ where

-- Синтаксические категории. Общая интерпретация
-- =============================================

-- Различение синтаксиса и семантики у Монтегю условно.


-- Предложения это пропозиции / типы
S = λ ℓ → Set ℓ

-- CN это просто множества / типы
CN = λ ℓ → Set ℓ                        -- CN ≠ e → t !

VP : ∀ {ℓ} → CN ℓ → S (lsuc ℓ)   -- VP = e → t           VP A = A → Set
VP {ℓ} A = A → Set ℓ 

NP : ∀ {ℓ} → CN ℓ → S (lsuc ℓ)   -- NP = (e → t) → t     NP A = (A → Set) → Set
NP {ℓ} A = VP A → Set ℓ

DET : ∀ {ℓ} → S (lsuc ℓ)         -- DET = (e → t) → ((e → t) → t) 
DET {ℓ} = (A : CN ℓ) → VP A → Set ℓ 

AP : ∀ {ℓ} → CN ℓ → CN (lsuc ℓ)  -- AP = (e → t) → (e → t)
AP {ℓ} A = A → Set ℓ

VI : ∀ {ℓ} → CN ℓ → S (lsuc ℓ)   -- VI = e → t
VI {ℓ} A = A → Set ℓ


-- Семантика
-- =========

postulate
  *Human : Set
  *Alex *Mary : *Human
  *runs : *Human → Set

Human : CN _
Human = *Human

runs-VI : VI *Human
runs-VI = *runs

vp-vi : ∀ {ℓ} {A : CN ℓ} → VI A → VP A
vp-vi v = v 

runs : VP *Human
runs = vp-vi runs-VI

np-pn : ∀ {ℓ} {A : CN ℓ} → A → NP A      -- NP {ℓ} A = (A → Set ℓ) → Set ℓ
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

a : ∀ {ℓ} → DET {ℓ}           -- DET {ℓ} = (A : Set ℓ) → (A → Set ℓ) → Set ℓ
a A v = Σ A v 
-- a A v = Σ[ x ∈ A ] v x 

every : ∀ {ℓ} → DET {ℓ}
every A v = (x : A) → v x

no : ∀ {ℓ} → DET {ℓ}
no A v = (x : A) → ¬ v x


a-human : NP *Human
a-human = a Human

s4 = a-human runs


every-human : NP *Human
every-human = every Human

s5 = every-human runs    


-- the domain of 'the' should be a singleton?
the : ∀ {ℓ} → DET {ℓ}
the A v = Σ[ x ∈ (Σ[ z ∈ A ] v z) ] Σ[ y ∈ A ] (y ≡ proj₁ x)

the-human : NP *Human
the-human = the Human

s6 = the-human runs

postulate
  *Mary-runs : *runs *Mary

_ : s6
_ = (*Mary , *Mary-runs) , *Mary , refl



-- Другой способ

s7 = (a Human) runs  

s8 = (every Human) runs  

s9 = (no Human) runs

s10 = (the Human) runs




-- Прилагательные / свойства

postulate
  *big : *Dog → Set
  *polkan-is-big : *big *Polkan

ap-a : ∀ {ℓ} {A : CN ℓ} → (A → Set ℓ) → AP A
ap-a x = x

big : AP *Dog
big = ap-a *big


cn-ap : ∀ {ℓ} {A : CN ℓ} {ap : AP A} → (x : A) → (ap x) → Σ A ap
cn-ap x px = x , px

big-dog : Σ *Dog big
big-dog = cn-ap *Polkan *polkan-is-big


-- cn-ap корректно:

_ : ∀ {ℓ} {A : CN ℓ} {ap : AP A} (x : A) → ap x → Σ A ap
_ = λ x px → cn-ap x px



-- Относительные конструкции (CN that VP и пр.)

RCN : ∀ {ℓ} (A : CN ℓ) → VP A → Set _
RCN A vp = Σ A vp

rcn : ∀ {ℓ} {A : CN ℓ} {vp : VP A} → (x : A) → vp x → RCN A vp 
rcn x vx = x , vx


Mary-that-runs : RCN *Human *runs
Mary-that-runs = rcn *Mary *Mary-runs

a-human-that-runs : NP (Σ *Human *runs)
a-human-that-runs = a (RCN *Human *runs)


--s11 = a-human-that-runs runs   -- не работает!  нужна коэрсия


postulate
  *sings : Σ *Human *runs → Set

sings = vp-vi *sings       -- должно быть vp-vi sings-VI, но я сократил

s12 = a-human-that-runs sings




