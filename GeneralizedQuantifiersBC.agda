-- See Barwise, Cooper - Generalized Quantifiers and Natural Language
{-# OPTIONS --cumulativity #-}

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _≥_; _>_)

module _ where

open import TTCore


-- Квантор это утверждение о типе всех x, таких, что P x.
-- Т.о. квантор это утверждение о Σ-типе.

-- Все кванторы имеют тип (A : Set) (v : A → Set) → Set

-- универсальный квантор
Qall : (A : Set) (v : A → Set) → Set 
Qall A v = ∀ (x : A) → v x      -- док-во = все пары; Σ-тип содержит все x : A

-- экзистенциальный квантор
Qsome : (A : Set) (v : A → Set) → Set 
Qsome A v = Σ A v               -- док-во = хотя бы одна пара; Σ-тип не пуст


-- Неопределённый дескриптор: "такой x, что v x".
-- Вообще, Σ-тип это неопределённый дескриптор.
-- То же используется в вопросах: What x, such that vx?
-- (What do I know? = What x, I know x?)

ι-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
ι-syntax = Σ 

syntax ι-syntax A (λ x → vx) = ι[ x ∈ A ] vx 

Qdesc : (A : Set) (v : A → Set) → Set
Qdesc A v = Σ A v

-- Вариант с неявным A
ι-syntax' : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
ι-syntax' {A = A} v = Σ A v 

syntax ι-syntax' (λ x → vx) = ι[ x ] vx 


-- "Ни один A не..."
Qno : (A : Set) (v : A → Set) → Set 
Qno A v = ⊥               -- т.е. Σ-тип пуст


--== артикль the ==

-- singleton
data The (A : Set) : Set where
  the : (a : A) → ((x : A) → x ≡ a) → The A 

-- тип пар (a , _), в которых a уникален.
-- это оператор (определённой) дескрипции (ιx)vx
private
  unthe : {A : Set} → The A → A
  unthe (the a _) = a

Qthe : (A : Set) (v : A → Set) → Set
Qthe A v = Σ (The A) λ x → v (unthe x)              -- док-во = любой уникальный a : A, такой, что v a


-- другое определение the,
-- уникальность содержится в кванторе
Qthe' : (A : Set) (v : A → Set) → Set
Qthe' A v = Σ A λ x → ((y : A) → y ≡ x) × v x


-- такой единственный x, что vx
ι!-syntax' : {A : Set} (v : A → Set) → Set
ι!-syntax' {A} v = Σ (The A) λ x → v (unthe x)

syntax ι!-syntax' (λ x → vx) = ι![ x ] vx

 

--== two elements type ==

data Both (A : Set) : Set where
  both : (a b : A) → a ≢ b → ((x : A) → (x ≡ a) ⊎ (x ≡ b)) → Both A 

Qboth : (A : Set) (v : A → Set) → Set 
Qboth A v = Σ (Both A) λ x → v (proj₁ (unboth x)) × v (proj₂ (unboth x))       -- док-во = две различные пары
  where
  unboth : {A : Set} → Both A → A × A
  unboth (both a b _ _) = (a , b)


--== ℕ elements types ==

-- power set
data P {ℓ} (A : Set ℓ) : Set (lsuc ℓ) where
  subs : (A → Set) → P A

postulate
  N= : {A : Set} (S : P A) (n : ℕ) → Set       -- N= S n => S has exactly n (different) elements
  N+ : {A : Set} (S : P A) (n : ℕ) → Set       -- N+ S n => S has minimum n (different) elements

-- subsets of A having exactly n elements
DN= : (A : Set) (n : ℕ) → Set₁
DN= A n = Σ (P A) (λ x → N= {A = A} x n)

getPred= : {A : Set} {n : ℕ} → DN= A n → (A → Set)
getPred= (subs f , _) = f

-- subsets of A having at least n elements
DN+ : (A : Set) (n : ℕ) → Set₁
DN+ A n = Σ (P A) (λ x → N+ {A = A} x n)

getPred+ : {A : Set} {n : ℕ} → DN+ A n → (A → Set)
getPred+ (subs f , _) = f


-- для некоторого подмножества S размера n, для каждого его элемента верно v
-- π: только три города...
Qℕ= : ∀ (n : ℕ) (A : Set) (v : A → Set) → Set₁
Qℕ= n A v = Σ[ S ∈ DN= A n ] ((x : Σ A (getPred= S)) → v (proj₁ x))

-- для некоторого подмножества S размера ≥ n, для каждого его элемента верно v
-- π: три города..., более дюжины...
Qℕ+ : ∀ (n : ℕ) (A : Set) (v : A → Set) → Set₁
Qℕ+ n A v = Σ[ S ∈ DN+ A n ] ((x : Σ A (getPred+ S)) → v (proj₁ x))


--== the most general case ==

-- type of subsets satisfying requirement req
DReq : ∀ {ℓ} (A : Set) (req : P A → Set ℓ) → Set (lsuc ℓ)
DReq A req = Σ (P A) λ S → req S

getPred : ∀ {ℓ} {A : Set} {req : P A → Set ℓ} → DReq A req → (A → Set)
getPred {req} (subs f , _) = f

-- for some S satisfying req all its elements are v
QReq : ∀ {ℓ} (A : Set) (v : A → Set) (req : P A → Set ℓ) → Set (lsuc ℓ)
QReq {ℓ} A v req = Σ[ S ∈ DReq {ℓ} A req ] ((x : Σ A (getPred {req = req} S)) → v (proj₁ x))



_ : ∀ {A : Set} {n : ℕ} → DN= A n ≡ DReq A (λ x → N= x n)
_ = refl


-- == PN - personal nouns ==

postulate
  boy  : Set
  John : boy
  runs : boy → Set
  jr : runs John

data PN (A : Set) : Set where
  pn : (a : A) → PN A
  
Qpn : ∀ {ℓ} {A : Set ℓ} (v : A → Set) (a : A) → Set ℓ 
Qpn v a = v a               -- v a непусто; т.е. (a , _) : Σ A v

Qpnj : (v : boy → Set) → Set
Qpnj v = Qpn v John 


-- John runs.
_ : Qpnj runs
_ = jr

-- Some boy runs.
_ : Qsome boy runs
_ = John , jr

-- x such that boy, runs   -- indefinite description
_ : Qdesc boy runs
_ = John , jr

_ : ι[ x ∈ boy ] runs x
_ = John , jr

_ : ι[ x ] runs x
_ = John , jr


-- TODO: prove this
-- postulate
--   Singleton : {A : Set} → (P A) → (a : A) → Set

-- _ : {A : Set} {v : A → Set} {a : A} → Qpn v a ≡ QReq A v (λ S → Singleton S a)
-- _ = refl



-- No boy runs.
S0 = Qno boy runs

-- ?
_ : ¬ (Qno boy runs)
_ = λ x → x

_ : Qsome boy runs → ¬ (Qno boy runs)
_ = λ _ z → z

-- Не доказывается из-за двойного отрицания
_ : ¬ (Qno boy runs) → Qsome boy runs
_ = {!!}


-- The boy runs.
postulate
  unq : (x : boy) → x ≡ John

_ : Qthe boy runs
_ = (the John unq) , jr

-- тот единственный x, который бежит
_ : ι![ x ] runs x
_ = (the John unq) , jr



-- == Кванторы как типы == --

-- Квантор = тип пар, удовлетворяющих некоторому условию.

-- определение аналогично Σ типу
data TQsome (A : Set) (P : A → Set) : Set where
  qsome : (a : A) (b : P a) → TQsome A P

-- То же, но определённое как запись.
-- record можно понимать как ситуацию.
record RQsome (A : Set) (P : A → Set) : Set where
  field
    fst : A
    snd : P fst

-- в исходной теории типов (не в Agda) это определение должно
-- совпадать с правилом для типа функций
data TQall (A : Set) (P : A → Set) : Set where
  qall : ((x : A) → P x) → TQall A P

record RQall (A : Set) (P : A → Set) : Set where
  field
    fun : (x : A) → P x

-- аналогично ⊥, нет конструкторов
data TQno (A : Set) (P : A → Set) : Set where

_ : ¬ (TQno boy runs)
_ = λ ()

data TBoth (A : Set) (P : A → Set) : Set where
  qboth : (a b : A) → (a ≡ b → ⊥) → ((x : A) → (x ≡ a) ⊎ (x ≡ b)) → TBoth A P


data TQthe (A : Set) (P : A → Set) : Set where
  qthe : (a : A) → P a → ((x : A) → x ≡ a) → TQthe A P 

record RQthe (A : Set) (P : A → Set) : Set where
  constructor rqthe
  field
    fst : A
    snd : P fst
    uniqueness : (x : A) → x ≡ fst
    
_ : TQthe boy runs
_ = qthe John jr unq

_ : RQthe boy runs
_ = rqthe John jr unq


-- то же, но уникальность выражается единственностью конструктора.
data girl : Set where
  Mary : girl

-- докажем уникальность
unq' : (x : girl) → x ≡ Mary
unq' Mary = refl

postulate
  runs' : girl → Set
  mr : runs' Mary

_ : TQthe girl runs'
_ = qthe Mary mr unq'

_ : RQthe girl runs'
_ = rqthe Mary mr unq'

-- all girls run
awr : (x : girl) → runs' x
awr Mary = mr

postulate
  _likes_ : boy → girl → Set
  jlm : John likes Mary

-- John likes the girl
_ : TQthe girl (λ x → John likes x)
_ = qthe Mary jlm unq'


-- John likes some girl
_ : TQsome girl (λ x → John likes x)
_ = qsome Mary jlm

unq'' : (x : girl) → John likes x
unq'' Mary = jlm

-- John likes all girls
_ : TQall girl (λ x → John likes x)
_ = qall unq''


-- some boy likes the girl
_ : TQsome boy (λ x → TQthe girl (λ y → x likes y))
_ = qsome John (qthe Mary jlm unq')

-- some boy likes all girls
_ : TQsome boy (λ x → TQall girl (λ y → x likes y))
_ = qsome John (qall unq'')

-- здесь вместо одного предложения 'a likes b' мы имеем семейство предложений
-- 'x likes y' для x, y, выбираемых соответственно кванторам.


-- Двусмысленность неопределённого артикля.

postulate
  mlm : (x : boy) → x likes Mary  -- every boy likes Mary
  mlw : (x : boy) → Σ girl (λ y → x likes y)
  
-- every boy likes a girl (the same)
_ : TQall boy (λ x → TQsome girl (λ y → x likes y))
_ = qall λ x → qsome Mary (mlm x)

-- (1) every boy likes a girl (his own)
_ : TQall boy (λ x → TQsome girl (λ y → x likes y))
_ = qall λ x → qsome (proj₁ (mlw x)) (proj₂ (mlw x))

-- Here types are the same but terms differ.
-- Ambiguity is reflected in terms, not in types.
-- This means that types are not enough to express meanings!

-- The first meaning _can_ be expressed differently:

-- (2) there is a girl every boy likes
_ : TQsome girl (λ y → TQall boy (λ x → x likes y))
_ = qsome Mary (qall mlm)

-- But the second meaning can _not_ be written unambiguously, can it?

-- maybe this way? unlikely
_ : TQall boy (λ x → TQsome (Σ girl (λ y → x likes y)) (λ z → x likes (proj₁ z)))
_ = qall (λ x → qsome (mlw x) (proj₂ (mlw x)))

-- Anyway, the condition that girls are different should be stated separately.

-- See Ranta TTG, 3.2 (about the precedence of quantifiers).


-- В (2) явно сказано, что девочка одна и та же. Но в (1) это не сказано явно; поэтому
-- может так оказаться, что она одна, а может и нет.  Поэтому (1) имеет оба
-- доказательства -- и для одной девочки, и для разных.



-- == Personal nouns ==

data TQpn {A : Set} (a : A) (P : A → Set) : Set where
  qpn : P a → TQpn a P

-- Mary runs
_ : TQpn Mary runs' 
_ = qpn mr

-- John runs
_ : TQpn John runs 
_ = qpn jr


-- situation "name" + "P name"
record RQpn {A : Set} (name : A) (P : A → Set) : Set where
  constructor rqpn
  field
    p    : P name       -- condition on Σ A P

-- situation "Mary runs"
_ : RQpn Mary runs' 
_ = rqpn mr


-- == Continuations == --

CsomeA : {A : Set} → (C : A → Set) → Set
-- Csome A = (P : A → Set) → Σ A P
CsomeA {A} C = Qsome A C

Call : {A : Set} → (C : A → Set) → Set
-- Call A = (P : A → Set) → ((x : A) → P x)
Call {A} C = Qall A C

Cthe : (A : Set) → Set₁
Cthe A = (P : A → Set) → Qthe A P

-- ??
CsomeP : {A : Set} → (C : (A → Set) → Set) → Set₁
CsomeP {A} C = (P : A → Set) → Qsome A (λ x → (C P))

Cid : ∀ {ℓ} (A : Set ℓ) → Set ℓ
Cid A = A


Cpn : {A : Set} (a : A) → (P : A → Set) → Set _
Cpn {A} a = λ (P : A → Set) → Qpn P a

Cjohn : (boy → Set) → Set 
Cjohn = λ (C : boy → Set) → C John
Cruns = λ (C : (boy → Set) → Set) → C runs
Cruns' = λ (C : (girl → Set) → Set) → C runs'

-- John runs
S1 : ∀ {ℓ} {A : Set ℓ} → (Set → Set) → Set
S1 {A = A} = λ (C : Set → Set) → Cruns (λ P → (Cjohn (λ x → C (P x))))

_ : S1 {A = boy} Cid
_ = jr


-- some boy runs
S2 : {A : Set} → (Set → Set) → Set
S2 {A = boy} = λ (C : Set → Set) → Cruns (λ P → (CsomeA P)) 

_ : S2 {A = boy} Cid
_ = John , jr

-- -- some boy runs
-- S3 : ∀ {ℓ} {A : Set ℓ} → (Set → Set) → Set (lsuc ℓ)
-- S3 {A = boy} = λ (C : Set → Set) → CsomeP (λ P → (Cruns P)) 

-- _ : S3 {A = boy} Cid
-- _ = John , jr

-- all girls run
S4 : {A : Set} → (Set → Set) → Set
S4 {A = girl} = λ (C : Set → Set) → Cruns' (λ P → Call P)

_ : S4 {A = girl} Cid
_ = awr

