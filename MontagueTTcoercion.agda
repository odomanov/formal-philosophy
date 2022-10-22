-- Montague semantics in terms of TT.
-- With coercion.

open import TTCore
open import Coercion

module _ where

-- Синтаксические категории. Общая интерпретация
-- =============================================

-- Предложения это пропозиции / типы
S = λ ℓ → Set ℓ

-- CN это просто множества / типы
CN = λ ℓ → Set ℓ

VP : ∀ {ℓ} → CN ℓ → S (lsuc ℓ)         -- VP = e → t           VP A = A → Set
VP {ℓ} A = A → Set ℓ

NP : ∀ {ℓ} → CN ℓ → S (lsuc ℓ)         -- NP = (e → t) → t     NP A = (A → Set) → Set
NP {ℓ} A = ∀ {B : CN ℓ} → {{_ : A <: B}} → (B → Set ℓ) → Set ℓ

DET : ∀ {ℓ} → S (lsuc ℓ) 
DET {ℓ} = (A : CN ℓ) {B : CN ℓ} → {{_ : A <: B}} → (B → Set ℓ) → Set ℓ 

AP : ∀ {ℓ} → CN ℓ → CN (lsuc ℓ)
AP {ℓ} A = A → Set ℓ

VI : ∀ {ℓ} (A : CN ℓ) → S (lsuc ℓ)
VI {ℓ} A = A → Set ℓ


-- Семантика
-- =========

postulate
  *Animate *Human : Set
  *Alex *Mary : *Human
  *runs : *Animate → Set 

Human = *Human
Animate = *Animate

postulate
  fHA : Human → Animate
instance
  Ac : ∀ {ℓ} {A : CN ℓ} → A <: A
  Ac = identityCoercion
  HAc : Human <: Animate
  HAc = coerce fHA

  
-- VI как VP
vp-v : ∀ {ℓ} {A B : CN ℓ} → {{_ : A <: B}} → VI B → VP A
vp-v v x = v ⟪ x ⟫

runs : VP *Animate
runs = vp-v *runs

-- PN как NP
np-pn : ∀ {ℓ} {A : CN ℓ} → A → NP A
np-pn pn v = v ⟪ pn ⟫

Mary : NP *Human           -- Mary as a noun phrase
Mary = np-pn {A = *Human} *Mary 


s1 = Mary runs

s2 = (np-pn *Mary) runs



postulate
  *Dog : Set
  *Polkan : *Dog

Dog = *Dog

postulate
  fDA : Dog → Animate
  
instance
  DAc : Dog <: Animate
  DAc = coerce fDA
  
Polkan : NP *Dog
Polkan = np-pn {A = *Dog} *Polkan 


s3 = Polkan runs     -- работает!



--  Определители (артикли и пр.)

a : ∀ {ℓ} → DET {ℓ}                 -- DET {ℓ} = (A : CN ℓ) {B : CN ℓ} → {{_ : A <: B}} → (B → Set ℓ) → Set ℓ
a A v = Σ A (λ x → v ⟪ x ⟫) 

every : ∀ {ℓ} → DET {ℓ}
every A v = (x : A) → v ⟪ x ⟫

no : ∀ {ℓ} → DET {ℓ}
no A v = (x : A) → ¬ v ⟪ x ⟫


a-human : NP *Human
a-human = a *Human

s4 = a-human runs


every-human : NP *Human
every-human = every *Human

s5 = every-human runs    


the : ∀ {ℓ} → DET {ℓ}
the A v = Σ (Σ A (λ x → v ⟪ x ⟫)) (λ x → Σ A (λ y → y ≡ proj₁ x))

the-human = the *Human

s6 = the-human runs

postulate
  *Mary-runs : *runs ⟪ *Mary ⟫

_ : s6
_ = (*Mary , *Mary-runs) , *Mary , refl



-- Другой способ

s7 = (a Human) runs  

s8 = (every Human) runs  

s9 = (no Human) runs

s10 = (the Human) runs




-- Прилагательные / свойства

postulate
  *big : *Animate → Set
  *polkan-is-big : *big ⟪ *Polkan ⟫

ap-a : ∀ {ℓ} {A B : CN ℓ} {{_ : A <: B}} → (B → Set ℓ) → AP A
ap-a f x = f ⟪ x ⟫  

biga : AP *Animate
biga = ap-a *big

bigd : AP *Dog
bigd = ap-a *big

instance
  Σc : ∀ {a b} {A : CN a} {B : A → Set b} → Σ A B <: A
  Σc = coerce proj₁
  ΣHAc : ∀ {ℓ} {B : *Human → Set ℓ}  → Σ *Human B <: *Animate
  ΣHAc = coerce (fHA ∘ proj₁)

cn-ap : ∀ {ℓ} {A B : CN ℓ} {ap : AP B} → {{_ : A <: B}} → (x : A) → (ap ⟪ x ⟫) → (Σ A (λ y → ap ⟪ y ⟫))
cn-ap x px = ⟪ x ⟫ , px

big-dog : (Σ *Dog (ap-a *big)) -- bigd)
big-dog = cn-ap {B = *Dog} *Polkan *polkan-is-big


-- cn-ap корректно:

_ : ∀ {ℓ} {A : CN ℓ} {ap : AP A} (x : A) → ap x → (Σ A ap)
_ = λ x px → cn-ap x px





-- Относительные конструкции (CN that VP и пр.)

RCN : ∀ {ℓ} (A : CN ℓ) {B : CN ℓ} → {{_ : A <: B}} → VP B → Set ℓ
RCN A vp = (Σ A (λ x → vp ⟪ x ⟫))

rcn : ∀ {ℓ} {A B : CN ℓ} {ap : AP B} → {{_ : A <: B}} → (x : A) → (ap ⟪ x ⟫) → RCN A ap -- (λ y → ap ⟪ y ⟫)
-- rcn : ∀ {ℓ} {A : CN ℓ} {vp : VP A} → (x : A) → vp x → RCN A vp 
rcn x vx = ⟪ x ⟫ , vx


Mary-that-runs : RCN *Human *runs
Mary-that-runs = rcn {B = *Human} *Mary *Mary-runs

a-human-that-runs : NP (Σ *Human _)
a-human-that-runs = a (RCN *Human *runs)


s11 = a-human-that-runs runs   -- работает! 

-- s11 = Σ (Σ *Human (λ x → *runs (fHA x))) (λ x → *runs (fHA (proj₁ x)))


s11' = (np-pn Mary-that-runs) runs

_ : s11'
_ = *Mary-runs 



postulate
  *singsa : VI *Animate 
  *singsh : VI *Human 

singsa : VP *Animate
singsa = vp-v *singsa  

-- s12 = Σ (Σ *Human (λ x → *runs (fHA x))) (λ x → *singsa (fHA (proj₁ x)))

s12 = a-human-that-runs singsa

singsh : VP *Human
singsh = vp-v *singsh  

-- s13 = Σ (Σ *Human (λ x → *runs (fHA x))) (λ x → *singsh (proj₁ x))

s13 = a-human-that-runs singsh




