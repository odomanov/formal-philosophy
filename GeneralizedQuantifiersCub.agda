-- See: 1) Barwise, Cooper - Generalized Quantifiers and Natural Language
--      2) Keenan, E. and Y. Stavi (1983) “A Semantic Characterization of
--         Natural Language Determiners,” Linguistics and Philosophy 9:
--         253–326
{-# OPTIONS --cubical --cumulativity #-}

module _ where

open import Cubical.Core.Everything
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; znots)
open import Cubical.Data.Nat.Order using (_≥_; _>_)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.HITs.PropositionalTruncation.Base 
open import Cubical.Foundations.Everything
  using (refl; subst; section; _∘_; singl; sym; cong; _∙_)
open import Cubical.Relation.Nullary using (¬_)


-- Определитель и усечённый Σ-тип
-- ==============================

DET : ∀ {ℓ ℓ'} → Type (ℓ-suc (ℓ-max ℓ ℓ'))
DET {ℓ} {ℓ'} = (A : Type ℓ) (v : A → Type ℓ') → Type (ℓ-max ℓ ℓ') 

-- Определители ниже это утверждения о ∃-типе
∃ : ∀ {ℓ ℓ'} (A : Type ℓ) (v : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
∃ A v = Σ A (λ x → ∥ v x ∥₁)                                        -- truncation



-- Основные определители
-- =====================

-- Универсальный квантор как утверждение о ∃-типе.
-- Первая проекция имеет обратную функцию. В частности, это
-- означает, что существует биекция между A и ∃ A v, то есть
-- они равномощны.
Every : DET 
Every A v = Σ[ inv ∈ (A → ∃ A v) ] (section fst inv)

-- традиционное определение универсального квантора (с усечением)
Every' : DET
Every' A v = ∀ (x : A) → ∥ v x ∥₁       

-- -- Два определения эквивалентны.
t-all : (A : Type)(v : A → Type) → Every A v → Every' A v
t-all A v p x = subst (λ x → ∥ v x ∥₁) (snd p x) (snd (fst p x))

t-all' : ∀ A v → Every' A v → Every A v
t-all' A v p = (λ x → x , (p x)) , (λ b → refl)


-- Кванторы как утверждения о мощности ∃-типа
---------------------------------------------

-- должно быть Iso?
_↔_ : ∀{ℓ ℓ'}(A : Type ℓ)(B : Type ℓ') → Type (ℓ-max ℓ ℓ') 
A ↔ B = (A → B) × (B → A)

-- Предположим, что мы умеем вычислять мощность:
postulate
  ∣_∣ : ∀{ℓ} (A : Type ℓ) → ℕ
  -- это должны быть теоремы, но мы постулируем
  ∣0∣ : ∀{ℓ ℓ'}(A : Type ℓ)(v : A → Type ℓ') → (∣ ∃ A v ∣ ≡ 0) ↔ ((x : A) → ¬_ {ℓ'} (v x))
  ∣1∣ : ∀{A v} → (∣ ∃ A v ∣ ≥ 1) ↔ (Σ[ x ∈ A ] v x)

-- Для Every (см. выше) утверждения о мощности недостаточно.
-- Требуется обратная первая проекция.

-- Для остальных кванторов достаточно:

Some : DET
Some A v = ∣ ∃ A v ∣ ≥ 1 

No : DET
No A v = ∣ ∃ A v ∣ ≡ 0

At-least : (n : ℕ) → DET
At-least n A v = ∣ ∃ A v ∣ ≥ n 

More-than : (n : ℕ) → DET
More-than n A v = ∣ ∃ A v ∣ > n

Both : DET
Both A v = ∣ ∃ A v ∣ ≡ 2


------------------------------------------------------------------------
-- некоторые традиционные определения

-- экзистенциальный квантор
Some' : DET   
Some' A v = Σ A v               -- док-во = хотя бы одна пара; Σ-тип не пуст

-- Оба определения эквивалентны.
t-some : ∀ A v → Some A v → Some' A v
t-some A v p = fst (∣1∣ {A} {v}) p

t-some' : ∀ A v → Some' A v → Some A v
t-some' A v p = snd (∣1∣ {A} {v}) p


-- "Ни один A не..."
No' : DET 
No' A v =  (x : A) → ¬ v x                -- т.е. Σ-тип пуст

-- Оба определения эквивалентны.
t-no : ∀ A v → No A v → No' A v
t-no A v p = fst (∣0∣ A v) p

t-no' : ∀ A v → No' A v → No A v
t-no' A v p = snd (∣0∣ A v) p


------------------------------------------------------------------------
--== артикль the ==

-- тип A с выделенным элементом
record Pointed (A : Type) : Type where
  field
    the : A
open Pointed

-- Pointed A это не синглетон и не contractible type из HoTT.
-- 
-- (x : Pointed A) означает, что в A имеется выделенный элемент, а именно,
-- the x. Синглетон это лишь один из способов выделения элемента. Выделение
-- это не синглетон, а скорее функция из синглетона.


-- "The" определено только для элементов Pointed A.
-- "The A v" означает, что в A есть один выделенный элемент, и он v.
The : (A : Type) → {aₚ : Pointed A} → (v : A → Type) → Type
The A {aₚ} v = v (the aₚ)

-- Таким образом, выражения с артиклем "the" осмысленны лишь в контексте
-- (aₚ : Pointed A).  Например, "the present king of France" бессмысленно,
-- поскольку здесь тип A = "present king of France" пуст.


------------------------------------------------------------------------
-- == PN - personal nouns ==

data PN (A : Type) : Type where
  pn : (a : A) → PN A
  
-- В терминах условия на ∃-тип
Pn : {A : Type} (a : A) (v : A → Type) → Type
Pn {A} a v = Σ[ σ ∈ ∃ A v ] fst σ ≡ a

-- традиционное определение
Pn' : {A : Type} (a : A) (v : A → Type) → Type  
Pn' a v = ∥ v a ∥₁               -- v a непусто; т.е. (a , _) : ∃ A v

-- Два определения эквивалентны.
t-pn : (A : Type) (a : A) (v : A → Type) → Pn a v → Pn' a v
t-pn A a v ((x , vx) , r) = subst (λ y → ∥ v y ∥₁) r vx 

t-pn' : (A : Type) (a : A) (v : A → Type) → Pn' a v → Pn a v
t-pn' A a v p = (a , p) , refl



------------------------------------------------------------------------
-- Примеры

postulate
  boy  : Type
  John : boy
  runs : boy → Type
  jr   : runs John

-- John runs.
_ : Pn John runs
_ = (John , ∣ jr ∣₁) , refl

-- Some boy runs.
_ : Some boy runs
_ = snd ∣1∣ (John , jr)


-- No boy runs.
S0 = No boy runs

-- ?
_ : ¬ (No boy runs)
_ = λ x → nbr x John jr
  where
  nbr : No boy runs → No' boy runs
  nbr = fst (∣0∣ boy runs) 

_ : Some boy runs → ¬ (No boy runs)
_ = λ n≥1 n≡0 → lem2 n≥1 n≡0 
  where
  +1≡suc : ∀ n → n + 1 ≡ suc n
  +1≡suc zero = refl
  +1≡suc (suc n) = cong suc (+1≡suc n)
  
  lem1 : ∀{x y z : ℕ} → ¬ y ≡ z → x ≡ y → x ≡ z → ⊥
  lem1 {z = z} ¬yz xy xz = ¬yz (subst (_≡ z) xy xz)

  lem2 : ∀{x} → Σ ℕ (λ k → k + 1 ≡ x) → x ≡ 0 → ⊥
  lem2 (k , p1) p0 = lem1 (znots {k}) p0 (sym p1 ∙ +1≡suc k)


_ : Some' boy runs → ¬ (No' boy runs)
_ = λ x z → z (fst x) (snd x)

-- Не доказывается из-за двойного отрицания
-- _ : ¬ (No' boy runs) → Some' boy runs
-- _ = {!!}


-- The boy runs.
_ : The boy {aₚ = record { the = John }} runs
_ = jr   


-- Производные определители
-- ========================

-- Определим операции на определителях, позволяющие строить определители из
-- других определителей.

infix 30 NOT _AND_ _OR_

-- Отрицание.
-- Но не все определители могут отрицаться -- например, the.
NOT : DET → DET
NOT d A v = d A (λ x → ¬ v x) --d A (∁ v)

_AND_ : DET → DET → DET
(d1 AND d2) A v = d1 A v × d2 A v

_OR_ : DET → DET → DET
(d1 OR d2) A v = d1 A v ⊎ d2 A v


-- Примеры производных определителей.

Fewer-than = NOT ∘ At-least

No-fewer-than = NOT ∘ Fewer-than

-- То же самое в другом определении
No-fewer-than' = NOT ∘ NOT ∘ At-least 

At-most = NOT ∘ More-than

Between_and_ : (n m : ℕ) → DET
Between n and m = At-least n AND At-most m

Exactly : (n : ℕ) → DET
Exactly n = Between n and n

No'' : DET
No'' = NOT Some

Only-some = Some AND (NOT Every)

-- Only-the = Every AND (λ A → No (∁ A))   --???

Either_or_ = _OR_

Neither_nor_ : DET → DET → DET
Neither d1 nor d2 = NOT (d1 OR d2)

_ : ∀ {d1 d2} → NOT (d1 OR d2) ≡ (NOT d1) OR (NOT d2)
_ = refl

Infinitely-many : DET
Infinitely-many A v = ∀ n → More-than n A v

Just-finitely-many : DET
Just-finitely-many A v = Σ[ n ∈ ℕ ] Exactly n A v



-- Примеры

postulate
  man cat : Type
  run : man → Type

every-man-runs = Every man run
a-man-runs = Some man run
not-every-man-runs = (NOT Every) man run
no-man-runs = (NOT Some) man run
no-man-runs' = No' man run
at-least-5-and-fewer-than-10-men-runs = ((At-least 5) AND (NOT (At-least 10))) man run



------------------------------------------------------------------------
-- == Continuations == --
-- See Barker Ch. - Continuations and the nature of quantification (2002).

CsomeA : {A : Type} → (C : A → Type) → Type
CsomeA {A} C = Some' A C

Call : {A : Type} → (C : A → Type) → Type
Call {A} C = Every' A C

Cthe : (A : Type) {aₚ : Pointed A} → Type₁
Cthe A {aₚ} = (v : A → Type) → The A {aₚ} v

-- ??
CsomeP : {A : Type} → (C : (A → Type) → Type) → Type₁
CsomeP {A} C = (v : A → Type) → Some' A (λ x → (C v))

Cid : ∀ {ℓ} (A : Type ℓ) → Type ℓ
Cid A = A


Cpn : {A : Type} (a : A) → (v : A → Type) → Type _
Cpn {A} a = λ (v : A → Type) → Pn' a v 

module _ where

  data girl : Type where
    Mary : girl
  
  postulate
    runs' : girl → Type
    mr : runs' Mary
  
  -- all girls run
  agr : (x : girl) → runs' x
  agr Mary = mr

Cjohn : (boy → Type) → Type 
Cjohn = λ (C : boy → Type) → C John
Cruns = λ (C : (boy → Type) → Type) → C runs
Cruns' = λ (C : (girl → Type) → Type) → C runs'

-- John runs
S1 : ∀ {ℓ} {A : Type ℓ} → (Type → Type) → Type
S1 = λ (C : Type → Type) → Cruns (λ v → (Cjohn (λ x → C (v x))))

_ : S1 {A = boy} Cid
_ = jr


-- some boy runs
S2 : {A : Type} → (Type → Type) → Type
S2 {A = boy} = λ (C : Type → Type) → Cruns (λ v → (CsomeA v)) 

_ : S2 {A = boy} Cid
_ = John , jr

-- some boy runs
-- S3 : ∀ {ℓ} {A : Type ℓ} → (Type → Type) → Type (ℓ-suc ℓ)
-- S3 {A = boy} = λ (C : Type → Type) → CsomeP (λ v → (Cruns v)) 

-- _ : S3 {A = boy} Cid
-- _ = John , jr

-- all girls run
S4 : {A : Type} → (Type → Type) → Type
S4 {A = girl} = λ (C : Type → Type) → Cruns' (λ v → Call v)

_ : S4 {A = girl} Cid
_ = λ x → ∣ agr x ∣₁ 



------------------------------------------------------------------------
-- Неопределённый дескриптор: "такой x, что v x", "тот A, что v".
-- Вообще, Σ-тип это неопределённый дескриптор.
-- То же используется в вопросах: What x, such that vx?
-- (What do I know? = What x, I know x?)

ι-syntax : ∀ {a b} (A : Type a) → (A → Type b) → Type (ℓ-max a b)
ι-syntax = Σ 

syntax ι-syntax A (λ x → vx) = ι[ x ∈ A ] vx 

Desc : DET
Desc A v = Σ A v

_ : Desc ≡ Some'
_ = refl

-- Вариант с неявным A
ι-syntax' : ∀ {a b} {A : Type a} → (A → Type b) → Type (ℓ-max a b)
ι-syntax' {A = A} v = Σ A v 

syntax ι-syntax' (λ x → vx) = ι[ x ] vx 

 
-- x such that boy, runs   -- indefinite description
_ : Desc boy runs
_ = John , jr

_ : ι[ x ∈ boy ] runs x
_ = John , jr

_ : ι[ x ] runs x
_ = John , jr

