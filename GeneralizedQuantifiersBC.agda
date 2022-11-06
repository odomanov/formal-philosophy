-- See Barwise, Cooper - Generalized Quantifiers and Natural Language

open import Nat using (ℕ; zero; suc; _≤_; _<_; _≥_; _>_)

module _ where

open import TTCore


-- Квантор это утверждение о типе всех x, таких, что P x.
-- Т.о. квантор это утверждение о Σ-типе.

-- Все кванторы имеют тип (A : Set) (v : A → Set) → Set
QUANTIFIER : ∀ {ℓ} → Set (lsuc ℓ)
QUANTIFIER {ℓ} = (A : Set) (v : A → Set) → Set ℓ


------------------------------------------------------------------------
-- универсальный квантор
Qall : QUANTIFIER
Qall A v = ∀ (x : A) → v x      -- док-во = все пары; Σ-тип содержит все x : A

-- Универсальный квантор как утверждение о Σ-типе.
-- Первая проекция имеет обратную функцию. В частности, это
-- означает, что существует биекция между A и Σ A v, то есть
-- они равномощны.
Qall' : QUANTIFIER
Qall' A v = Σ[ f⁻¹ ∈ (A → Σ A v) ] ∀ (x : A) → proj₁ (f⁻¹ x) ≡ x

-- Два определения эквивалентны.
t-all : ∀ A v → Qall' A v → Qall A v
t-all A v (f⁻¹ , ≡x) x = subst v (≡x x) (proj₂ (f⁻¹ x))

t-all' : ∀ A v → Qall A v → Qall' A v
t-all' A v p = (λ x → x , (p x)) , (λ x → refl)


------------------------------------------------------------------------
-- экзистенциальный квантор
Qsome : QUANTIFIER 
Qsome A v = Σ A v               -- док-во = хотя бы одна пара; Σ-тип не пуст

-- Экзистенциальный квантор как утверждение о Σ-типе.
-- Имеется хотя бы один элемент в Σ A v.
Qsome' : QUANTIFIER
Qsome' A v = Σ[ x ∈ Σ A v ] ⊤ 

-- Оба определения эквивалентны.
t-some : ∀ A v → Qsome' A v → Qsome A v
t-some A v p = proj₁ p

t-some' : ∀ A v → Qsome A v → Qsome' A v
t-some' A v p = p , tt



------------------------------------------------------------------------
-- "Ни один A не..."
Qno : QUANTIFIER 
Qno A v = (x : A) → ¬ v x -- ⊥               -- т.е. Σ-тип пуст


-- Определение как утверждение о Σ-типе.
-- Σ A v пуст.
Qno' : QUANTIFIER
Qno' A v = ¬ (Σ A v)


t-no : ∀ A v → Qno' A v → Qno A v
t-no A v p = λ x z → p (x , z)

t-no' : ∀ A v → Qno A v → Qno' A v
t-no' A v p x = p (proj₁ x) (proj₂ x)



------------------------------------------------------------------------
--== артикль the ==

-- тип A с выделенным элементом
record Pointed (A : Set) : Set where
  field
    the : A
open Pointed    

-- The определено только для типов Pointed A.
-- "The A v" означает, что в A есть один выделенный элемент, и он v.
Qthe : (A : Set) → {Aₚ : Pointed A} → (v : A → Set) → Set
Qthe A {Aₚ} v = v (the Aₚ)  



------------------------------------------------------------------------
--== two elements type ==

data Both (A : Set) : Set where
  both : (a b : A) → a ≢ b → ((x : A) → (x ≡ a) ⊎ (x ≡ b)) → Both A 

Qboth : QUANTIFIER 
Qboth A v =
  Σ (Both A) λ x → v (proj₁ (unboth x)) × v (proj₂ (unboth x))  -- док-во = две различные пары
  where
  unboth : {A : Set} → Both A → A × A
  unboth (both a b _ _) = (a , b)



------------------------------------------------------------------------
--== ℕ elements types ==

-- power set
data 𝒫 {ℓ} (A : Set ℓ) : Set (lsuc ℓ) where
  subs : (A → Set) → 𝒫 A

postulate
  N= : {A : Set} (S : 𝒫 A) (n : ℕ) → Set       -- N= S n => S has exactly n (different) elements
  N+ : {A : Set} (S : 𝒫 A) (n : ℕ) → Set       -- N+ S n => S has minimum n (different) elements

-- subsets of A having exactly n elements
DN= : (A : Set) (n : ℕ) → Set₁
DN= A n = Σ (𝒫 A) (λ x → N= {A = A} x n)

getPred= : {A : Set} {n : ℕ} → DN= A n → (A → Set)
getPred= (subs f , _) = f

-- subsets of A having at least n elements
DN+ : (A : Set) (n : ℕ) → Set₁
DN+ A n = Σ (𝒫 A) (λ x → N+ {A = A} x n)

getPred+ : {A : Set} {n : ℕ} → DN+ A n → (A → Set)
getPred+ (subs f , _) = f


-- Для некоторого подмножества S размера n, для каждого его элемента верно v.
-- π: только три города...
Qℕ= : ∀ (n : ℕ) → QUANTIFIER
Qℕ= n A v = Σ[ S ∈ DN= A n ] ((x : Σ A (getPred= S)) → v (proj₁ x))

-- Для некоторого подмножества S размера ≥ n, для каждого его элемента верно v.
-- π: три города..., более дюжины...
Qℕ+ : ∀ (n : ℕ) → QUANTIFIER
Qℕ+ n A v = Σ[ S ∈ DN+ A n ] ((x : Σ A (getPred+ S)) → v (proj₁ x))




------------------------------------------------------------------------
-- == PN - personal nouns ==

data PN (A : Set) : Set where
  pn : (a : A) → PN A
  
Qpn : {A : Set} (a : A) (v : A → Set) → Set  
Qpn a v = v a               -- v a непусто; т.е. (a , _) : Σ A v

-- То же в терминах условия на Σ-тип
Qpn' : {A : Set} (a : A) (v : A → Set) → Set
Qpn' {A} a v = Σ[ σ ∈ Σ A v ] proj₁ σ ≡ a

-- Два определения эквивалентны.
t-pn : (A : Set) (a : A) (v : A → Set) → Qpn' a v → Qpn a v
t-pn A a v ((x , vx) , r) = subst v r vx

t-pn' : (A : Set) (a : A) (v : A → Set) → Qpn a v → Qpn' a v
t-pn' A a v p = (a , p) , refl



------------------------------------------------------------------------
-- Примеры

postulate
  boy  : Set
  John : boy
  runs : boy → Set
  jr   : runs John

-- John runs.
_ : Qpn John runs
_ = jr

-- Some boy runs.
_ : Qsome boy runs
_ = John , jr


-- No boy runs.
S0 = Qno boy runs

-- ?
_ : ¬ (Qno boy runs)
_ = λ x → x John jr

_ : Qsome boy runs → ¬ (Qno boy runs)
_ = λ x z → z (proj₁ x) (proj₂ x)

-- Не доказывается из-за двойного отрицания
_ : ¬ (Qno boy runs) → Qsome boy runs
_ = {!!}


-- The boy runs.
_ : Qthe boy {Aₚ = record { the = John }} runs
_ = jr   





------------------------------------------------------------------------
-- == Кванторы как типы == --

-- Квантор = тип пар, удовлетворяющих некоторому условию.

-- определение аналогично Σ типу
data TQsome (A : Set) (v : A → Set) : Set where
  qsome : (a : A) (va : v a) → TQsome A v

-- То же, но определённое как запись.
-- record можно понимать как ситуацию.
record RQsome (A : Set) (v : A → Set) : Set where
  field
    a  : A
    va : v a

-- в исходной теории типов (не в Agda) это определение должно
-- совпадать с правилом для типа функций
data TQall (A : Set) (v : A → Set) : Set where
  qall : ((x : A) → v x) → TQall A v

record RQall (A : Set) (v : A → Set) : Set where
  field
    fun : (x : A) → v x

-- аналогично ⊥, нет конструкторов
data TQno (A : Set) (v : A → Set) : Set where

_ : ¬ (TQno boy runs)
_ = λ ()

data TBoth (A : Set) (v : A → Set) : Set where
  qboth : (a b : A) → a ≢ b → ((x : A) → (x ≡ a) ⊎ (x ≡ b)) → TBoth A v


data TQthe (A : Set) {Aₚ : Pointed A} (v : A → Set) : Set where
  qthe : v (the Aₚ) → TQthe A v 

record RQthe (A : Set) {Aₚ : Pointed A} (v : A → Set) : Set where
  constructor rqthe
  field
    va : v (the Aₚ)
    
_ : TQthe boy {record { the = John }} runs
_ = qthe jr 

_ : RQthe boy {record { the = John }} runs
_ = rqthe jr


data girl : Set where
  Mary : girl

postulate
  runs' : girl → Set
  mr : runs' Mary

_ : TQthe girl {record { the = Mary }} runs'
_ = qthe mr

_ : RQthe girl {record {the = Mary}} runs'
_ = rqthe mr

-- all girls run
awr : (x : girl) → runs' x
awr Mary = mr

postulate
  _likes_ : boy → girl → Set
  jlm : John likes Mary

-- John likes the girl
_ : TQthe girl {record {the = Mary}} (λ x → John likes x)
_ = qthe jlm


-- John likes some girl
_ : TQsome girl (λ x → John likes x)
_ = qsome Mary jlm


-- John likes all girls
_ : TQall girl (λ x → John likes x)
_ = qall λ { Mary → jlm }


-- some boy likes the girl
_ : TQsome boy (λ x → TQthe girl {record { the = Mary }} (λ y → x likes y))
_ = qsome John (qthe jlm)

-- some boy likes all girls
_ : TQsome boy (λ x → TQall girl (λ y → x likes y))
_ = qsome John (qall λ { Mary → jlm })

-- здесь вместо одного предложения 'a likes b' мы имеем семейство предложений
-- 'x likes y' для x, y, выбираемых соответственно кванторам.


-- Двусмысленность неопределённого артикля.

postulate
  blm : (x : boy) → x likes Mary  -- every boy likes Mary
  blg : (x : boy) → Σ girl (λ y → x likes y)
  
-- every boy likes a girl (the same)
_ : TQall boy (λ x → TQsome girl (λ y → x likes y))
_ = qall λ x → qsome Mary (blm x)

-- (1) every boy likes a girl (his own)
_ : TQall boy (λ x → TQsome girl (λ y → x likes y))
_ = qall λ x → qsome (proj₁ (blg x)) (proj₂ (blg x))

-- Here types are the same but terms differ.
-- Ambiguity is reflected in terms, not in types.
-- This means that types are not enough to express meanings!

-- The first meaning _can_ be expressed differently:

-- (2) there is a girl every boy likes
_ : TQsome girl (λ y → TQall boy (λ x → x likes y))
_ = qsome Mary (qall blm)

-- But the second meaning can _not_ be written unambiguously, can it?

-- maybe this way? unlikely
_ : TQall boy (λ x → TQsome (Σ girl (λ y → x likes y)) (λ z → x likes (proj₁ z)))
_ = qall (λ x → qsome (blg x) (proj₂ (blg x)))

-- Anyway, the condition that girls are different should be stated separately.

-- See Ranta TTG, 3.2 (about the precedence of quantifiers).


-- В (2) явно сказано, что девочка одна и та же. Но в (1) это не сказано явно; поэтому
-- может так оказаться, что она одна, а может и нет.  Поэтому (1) имеет оба
-- доказательства -- и для одной девочки, и для разных.



-- == Personal nouns ==

data TQpn {A : Set} (a : A) (v : A → Set) : Set where
  qpn : v a → TQpn a v

-- Mary runs
_ : TQpn Mary runs' 
_ = qpn mr

-- John runs
_ : TQpn John runs 
_ = qpn jr


-- situation "name" + "v name"
record RQpn {A : Set} (name : A) (v : A → Set) : Set where
  constructor rqpn
  field
    p    : v name       -- condition on Σ A v

-- situation "Mary runs"
_ : RQpn Mary runs' 
_ = rqpn mr




------------------------------------------------------------------------
-- == Continuations == --
-- See Barker Ch. - Continuations and the nature of quantification (2002).

CsomeA : {A : Set} → (C : A → Set) → Set
-- Csome A = (v : A → Set) → Σ A v
CsomeA {A} C = Qsome A C

Call : {A : Set} → (C : A → Set) → Set
-- Call A = (v : A → Set) → ((x : A) → v x)
Call {A} C = Qall A C

Cthe : (A : Set) {Aₚ : Pointed A} → Set₁
Cthe A {Aₚ} = (v : A → Set) → Qthe A {Aₚ} v

-- ??
CsomeP : {A : Set} → (C : (A → Set) → Set) → Set₁
CsomeP {A} C = (v : A → Set) → Qsome A (λ x → (C v))

Cid : ∀ {ℓ} (A : Set ℓ) → Set ℓ
Cid A = A


Cpn : {A : Set} (a : A) → (v : A → Set) → Set _
Cpn {A} a = λ (v : A → Set) → Qpn a v 

Cjohn : (boy → Set) → Set 
Cjohn = λ (C : boy → Set) → C John
Cruns = λ (C : (boy → Set) → Set) → C runs
Cruns' = λ (C : (girl → Set) → Set) → C runs'

-- John runs
S1 : ∀ {ℓ} {A : Set ℓ} → (Set → Set) → Set
S1 {A = A} = λ (C : Set → Set) → Cruns (λ v → (Cjohn (λ x → C (v x))))

_ : S1 {A = boy} Cid
_ = jr


-- some boy runs
S2 : {A : Set} → (Set → Set) → Set
S2 {A = boy} = λ (C : Set → Set) → Cruns (λ v → (CsomeA v)) 

_ : S2 {A = boy} Cid
_ = John , jr

-- -- some boy runs
-- S3 : ∀ {ℓ} {A : Set ℓ} → (Set → Set) → Set (lsuc ℓ)
-- S3 {A = boy} = λ (C : Set → Set) → CsomeP (λ v → (Cruns v)) 

-- _ : S3 {A = boy} Cid
-- _ = John , jr

-- all girls run
S4 : {A : Set} → (Set → Set) → Set
S4 {A = girl} = λ (C : Set → Set) → Cruns' (λ v → Call v)

_ : S4 {A = girl} Cid
_ = awr



------------------------------------------------------------------------
-- Неопределённый дескриптор: "такой x, что v x", "тот A, что v".
-- Вообще, Σ-тип это неопределённый дескриптор.
-- То же используется в вопросах: What x, such that vx?
-- (What do I know? = What x, I know x?)

ι-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
ι-syntax = Σ 

syntax ι-syntax A (λ x → vx) = ι[ x ∈ A ] vx 

Qdesc : QUANTIFIER
Qdesc A v = Σ A v

-- Вариант с неявным A
ι-syntax' : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
ι-syntax' {A = A} v = Σ A v 

syntax ι-syntax' (λ x → vx) = ι[ x ] vx 


 
-- x such that boy, runs   -- indefinite description
_ : Qdesc boy runs
_ = John , jr

_ : ι[ x ∈ boy ] runs x
_ = John , jr

_ : ι[ x ] runs x
_ = John , jr

