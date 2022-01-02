-- See Barwise, Cooper - Generalized Quantifiers and Natural Language

open import TTCore
open import Agda.Builtin.Equality


-- квантор это утверждение о типе всех x, таких, что P x.
-- Т.о. квантор это утверждение о Σ-типе.

-- Все кванторы имеют тип (A : Set) (v : A → Set) → Set

-- универсальный квантор
Qall : (A : Set) (v : A → Set) → Set 
Qall A v = ∀ (x : A) → v x      -- док-во = все пары; Σ-тип содержит все x : A

-- экзистенциальный квантор
Qsome : (A : Set) (v : A → Set) → Set 
Qsome A v = Σ A v               -- док-во = хотя бы одна пара; Σ-тип не пуст

Qno : (A : Set) (v : A → Set) → Set 
Qno A v = ⊥               -- т.е. Σ-тип пуст


-- артикль the --

-- singleton
data The (A : Set) : Set where
  the : (a : A) → ((x : A) → x ≡ a) → The A 

-- тип пар (a , _), в которых a уникален
Qthe : (A : Set) (v : A → Set) → Set
Qthe A v = Σ (The A) λ x → v (unthe x)              -- док-во = любой уникальный a : A, такой, что v a
  where
  unthe : {A : Set} → The A → A
  unthe (the a _) = a


-- другое определение the,
-- уникальность содержится в кванторе
Qthe' : (A : Set) (v : A → Set) → Set
Qthe' A v = Σ A λ x → ((y : A) → y ≡ x) × v x


-- two element type
data Both (A : Set) : Set where
  both : (a b : A) → (a ≡ b → ⊥) → ((x : A) → x ≡ a × x ≡ b) → Both A 

Qboth : (A : Set) (v : A → Set) → Set 
Qboth A v = Σ (Both A) λ x → v (proj₁ (unboth x)) × v (proj₂ (unboth x))       -- док-во = две различные пары
  where
  unboth : {A : Set} → Both A → A × A
  unboth (both a b _ _) = (a , b)


-- PN - personal nouns --

postulate
  man : Set
  John : man
  runs : man → Set
  jr : runs John

data PN (A : Set) : Set where
  pn : (a : A) → PN A
  
Qpn : {A : Set} (v : A → Set) (a : A) → Set 
Qpn v a = v a               -- v a непусто; т.е. (a , _) : Σ A v

Qpnj : (v : man → Set) → Set
Qpnj v = Qpn v John 


-- John runs.
_ : Qpnj runs
_ = jr

-- Some man runs.
_ : Qsome man runs
_ = John , jr

-- No man runs.
S3 = Qno man runs

-- ?
_ : ¬ (Qno man runs)
_ = λ x → x

-- The man runs.
postulate
  unq : (x : man) → x ≡ John

_ : Qthe man runs
_ = (the John unq) , jr


-- == Кванторы как типы == --

-- Квантор = тип пар, удовлетворяющих некоторому условию.

-- определение аналогично Σ типу
data TQsome (A : Set) (P : A → Set) : Set where
  qsome : (a : A) (b : P a) → TQsome A P

-- record можно понимать как ситуацию
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

-- ?
_ : ¬ (TQno man runs)
_ = λ ()

data TBoth (A : Set) (P : A → Set) : Set where
  qboth : (a b : A) → (a ≡ b → ⊥) → ((x : A) → x ≡ a × x ≡ b) → TBoth A P


data TQthe (A : Set) (P : A → Set) : Set where
  qthe : (a : A) → P a → ((x : A) → x ≡ a) → TQthe A P 

record RQthe (A : Set) (P : A → Set) : Set where
  constructor rqthe
  field
    fst : A
    snd : P fst
    uniqueness : (x : A) → x ≡ fst
    
_ : TQthe man runs
_ = qthe John jr unq

_ : RQthe man runs
_ = rqthe John jr unq


-- то же, но уникальность выражается единственностью конструктора.
data woman : Set where
  Mary : woman

-- докажем уникальность
unq' : (x : woman) → x ≡ Mary
unq' Mary = refl

postulate
  runs' : woman → Set
  mr : runs' Mary

_ : TQthe woman runs'
_ = qthe Mary mr unq'

_ : RQthe woman runs'
_ = rqthe Mary mr unq'



postulate
  _loves_ : man → woman → Set
  jlm : John loves Mary

-- John loves the woman
_ : TQthe woman (λ x → John loves x)
_ = qthe Mary jlm unq'


-- John loves some woman
_ : TQsome woman (λ x → John loves x)
_ = qsome Mary jlm

unq'' : (x : woman) → John loves x
unq'' Mary = jlm

-- John loves all women
_ : TQall woman (λ x → John loves x)
_ = qall unq''


-- some man loves the woman
_ : TQsome man (λ x → TQthe woman (λ y → x loves y))
_ = qsome John (qthe Mary jlm unq')

-- some man loves all women
_ : TQsome man (λ x → TQall woman (λ y → x loves y))
_ = qsome John (qall unq'')


-- PN

data TQpn {A : Set} (a : A) (P : A → Set) : Set where
  qpn : P a → TQpn a P

-- Mary runs
_ : TQpn Mary runs' 
_ = qpn mr

-- John runs
_ : TQpn John runs 
_ = qpn jr
