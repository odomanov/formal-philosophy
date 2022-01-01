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

data The (A : Set) : Set where
  the : (a : A) → ((x : A) → x ≡ a) → The A 

Qthe : (A : Set) (v : A → Set) → Set
Qthe A v = Σ (The A) λ x → v (unthe x)              -- док-во = любой уникальный a : A, такой, что v a
  where
  unthe : {A : Set} → The A → A
  unthe (the a _) = a


data Both (A : Set) (P : A → Set) : Set where
  both : (a b : A) → (P a) → (P b) → (a ≡ b → ⊥) → ((x : A) → (P x) → x ≡ a × x ≡ b) → Both A P

Qboth : (A : Set) (v : A → Set) → Set 
Qboth A v = Both A v               -- док-во = две различные пары


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
