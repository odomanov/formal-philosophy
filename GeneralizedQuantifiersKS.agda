-- See: Keenan, E. and Y. Stavi (1983) “A Semantic Characterization of Natural Language Determiners,”
--      Linguistics and Philosophy 9: 253–326

module _ where

open import TTCore
open import Nat using (ℕ; zero; suc; _≤_; _<_; _≥_; _>_)


-- Кванторы это утверждения о подмножествах. Поэтому импортируем Subsets.

import Subsets renaming (Subset to S)

postulate E : Set
open Subsets E                         -- Рассматриваем подмножества множества E.



-- Основные определители
-- =====================

-- Мы рассматриваем предикаты (например, глаголы) как подмножества.

Det = S → S → Set     -- (E → Set) → ((E → Set) → Set) 

-- Можно было бы определить просто:
module simple where

  Every : Det
  Every s v = s ⊆ v  -- ∀ {e} → s e → v e  
  
  Some : Det
  Some s v = Σ E (s ∩ v)

-- Но мы определим сложнее в общем виде.

-- Предположим, что мы умеем вычислять мощность:
postulate ∥_/_∥ : S → S → ℕ       -- Мощность s, таких, что v (с учётом дублирования v e).
                                  -- Здесь v (предикат, глагол) это тоже подмножество, как и s.

∥_∥ = λ s → ∥ s / s ∥             -- мощность s

infix 3 ∥_/_∥ ∥_∥


-- Кванторы как утверждения о мощности.

Every : Det
Every s v = ∥ s / v ∥ ≡ ∥ s ∥              -- = ∀ e : s → v

Some : Det
Some s v = ∥ s / v ∥ ≥ 1                   -- = ∃ e → s ∩ v

No : Det
No s v = ∥ s / v ∥ ≡ 0

At-least : (n : ℕ) → Det
At-least n s v = ∥ s / v ∥ ≥ n 

More-than : (n : ℕ) → Det
More-than n s v = ∥ s / v ∥ > n

Both' : {s : S} → {_ : ∥ s ∥ ≡ 2} → Det
Both' s v = Every s v                      -- ∥ s / v ∥ ≡ ∥ s ∥


-- Множество с одним элементом.
Singleton : E → S
Singleton a e = e ≡ a 

singlx≡a : ∀ {x a} → x ∈ (Singleton a) → x ≡ a
singlx≡a refl = refl

-- Собственные имена
PName : (J : E) → Det
PName J _ = Some (Singleton J) 

-- Определённый артикль.
The : (J : E) (s : S) → {_ : J ∈ s} → (v : S) → Set
The J s v = Every (Singleton J) v

-- Множественное 'the'
The-p : (s0 : S) (s : S) → {_ : s0 ⊆ s} → (v : S) → Set
The-p s0 s v = Every s0 v

Singl∈→⊆ : {J : E} (s : S) → (J ∈ s) → (Singleton J) ⊆ s
Singl∈→⊆ s J∈s e J≡e rewrite J≡e = J∈s

-- Единичное the -- частный случай множественного
The' : (J : E) (s : S) → {_ : J ∈ s} → (v : S) → Set
The' J s {J∈s} v = The-p (Singleton J) s {Singl∈→⊆ s J∈s} v  


-- TODO: This ...



-- == Объекты, принадлежащие кому-то ==

-- Предикат x владеет y:
postulate _own_ : E → E → Set

-- Всё, чем владеет J:
props : S → S
props J = λ e → Σ E (λ x → J x × x own e)

-- Все s, которыми владеет J (J's s)
_that_owns : S → S → S
s that J owns = s ∩ props J 

_`s_ : S → S → S
J `s s = s that J owns

-- Примеры.

-- every John's cat (sleeps)
Poss : Det → (J : S) → Det
Poss d J s v = d (J `s s) v

-- at least n John's cats
At-least-'s : S → ℕ → Det
At-least-'s J n s v = At-least n (J `s s) v

At-least-'s' : S → ℕ → Det
At-least-'s' J n = Poss (At-least n) J 

-- some John's cat
Some-'s : S → Det
Some-'s J = Poss Some J    

-- -- (the only) John's cat
-- _`s_ : S → Det
-- (J `s s) v = {x : ∥ props J ∥ ≡ 1} → Poss J 1 {x} s v

-- TODO: some student's, John's student's, etc.

-- some student's cat (sleeps)
Det's : Det → S → Det
Det's d stud = Poss d stud 

-- John's cat
PN's : (J : E) → Det
PN's J s v = Det's (PName J) U s v



-- Производные определители
-- ========================

-- Определим операции на определителях, позволяющие строить определители из
-- других определителей.

infix 30 NOT _AND_ _OR_

-- Отрицание.
-- Но не все определители могут отрицаться -- например, the.
NOT : Det → Det
NOT d s v = d s (∁ v)

_AND_ : Det → Det → Det
(d1 AND d2) s v = d1 s v × d2 s v

_OR_ : Det → Det → Det
(d1 OR d2) s v = d1 s v ⊎ d2 s v


-- Примеры производных определителей.

Fewer-than = NOT ∘ At-least

No-fewer-than = NOT ∘ Fewer-than

-- То же самое в другом определении
No-fewer-than' = NOT ∘ NOT ∘ At-least 

At-most = NOT ∘ More-than

Between_and_ : (n m : ℕ) → Det
Between n and m = At-least n AND At-most m

Exactly : (n : ℕ) → Det
Exactly n = Between n and n

No' : Det
No' = NOT Some

Only-some = Some AND (NOT Every)

Only-the = Every AND (λ s → No (∁ s))   --???

Either_or_ = _OR_

Neither_nor_ : Det → Det → Det
Neither d1 nor d2 = NOT (d1 OR d2)

_ : ∀ {d1 d2} → NOT (d1 OR d2) ≡ (NOT d1) OR (NOT d2)
_ = refl

Infinitely-many : Det
Infinitely-many s v = ∀ n → More-than n s v

Just-finitely-many : Det
Just-finitely-many s v = Σ[ n ∈ ℕ ] Exactly n s v



-- Примеры

postulate
  man cat : S
  run : S
  eMaxim ePeter : E

Maxim = Singleton eMaxim
Peter  = Singleton ePeter

every-man-runs = Every man run
a-man-runs = Some man run
not-every-man-runs = (NOT Every) man run
no-man-runs = (NOT Some) man run
at-least-5-and-fewer-than-10-men-runs = ((At-least 5) AND (NOT (At-least 10))) man run
Maxim's-cat-runs = Some (Maxim `s cat) run
Maxim's-and-Peter's-cat-run  = ((λ x → (Some (Maxim `s x))) AND (λ x → (Some (Peter `s x)))) cat run
Maxim's-and-Peter's-cat-run' = ((Some ∘ Maxim `s_) AND (Some ∘ Peter `s_)) cat run
every-Maxim's-and-some-Peter's-cat-run  = ((Every ∘ Maxim `s_) AND (Some ∘ Peter `s_)) cat run
