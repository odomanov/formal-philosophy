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

-- x уникален, но P x может не быть уникальным
data The (A : Set) (P : A → Set) : Set where
  the : (a : A) → P a → ((x : A) → P x → x ≡ a) → The A P

Qthe : (A : Set) (v : A → Set) → Set
Qthe A v = The A v             -- док-во = любой уникальный a : A, такой, что v a


-- другое определение the (неверное!) --

data Unique (A : Set) : Set where
  unique : (a : A) → ((x : A) → x ≡ a) → Unique A

-- не совсем верно! Σ не обязано быть уникальным
Qthe' : (A : Set) (v : A → Set) → Set 
Qthe' A v = Unique (Σ A v)

-- это верно, но обратное не обязательно верно
prf1 : ∀ (A : Set) (v : A → Set) → Qthe' A v → Qthe A v
prf1 A _ (unique a eq) = l2 a eq
  where
  l1 : {P : A → Set} (x : A) (p : P x) (a : Σ A P) → ((x , p) ≡ a) → x ≡ proj₁ a
  l1 _ _ _ refl = refl

  l2 : {P : A → Set} (a : Σ A P) → ((x : Σ A P) → x ≡ a) → The A P
  l2 a f = the (proj₁ a) (proj₂ a) λ x p → l1 x p a (f (x , p))


data Both (A : Set) (P : A → Set) : Set where
  both : (a b : A) → (P a) → (P b) → (a ≡ b → ⊥) → ((x : A) → (P x) → x ≡ a × x ≡ b) → Both A P

Qboth : (A : Set) (v : A → Set) → Set 
Qboth A v = Both A v               -- док-во = две различные пары


-- PN - personal nouns --

postulate
  man : Set
  John : man
  runs : man → Set

data PN (A : Set) : Set where
  pn : (a : A) → PN A
  
Qpn : {A : Set} (v : A → Set) (a : A) → Set 
Qpn v a = v a               -- v a непусто; т.е. (a , _) : Σ A v

Qpnj : (v : man → Set) → Set
Qpnj v = Qpn v John 


-- John runs.
S1 = Qpnj runs

-- Some man runs.
S2 = Qsome man runs

-- No man runs.
S3 = Qno man runs
