-- Montague semantics

-- https://en.wikipedia.org/wiki/Montague_grammar
-- https://plato.stanford.edu/entries/montague-semantics/


-- e, t это типы выражений языка.
-- e обозначает тип индивидов, t -- тип пропозиций или формул.

module Montague (e : Set) where         

{---- Семантика по Монтегю на языке логики предикатов.
      Словам (точнее, грамматическим категориям) соответствуют некоторые функции.

       CN   predicate              λx.predicate (x) 
       NP   DET CN                 (DET CN)                           DET = CN → NP
       NP   name                   λP. (P name)                       NP = P → S
       DET  "some"                 λP.λQ.∃x ((P x) ∧ (Q x))           S = DET p q
       DET  "a"                    λP.λQ.∃x ((P x) ∧ (Q x)) 
       DET  "every"                λP.λQ.∀x ((P x) → (Q x)) 
       DET  "no"                   λP.λQ.∀x ((P x) → (¬ (Q x))) 
       VI   intransverb            λx.intransverb (x)
       VT   transverb              λx.λy.transverb (x , y) 
       VP   VI                                                        VP = VI
       VP   VT NP                  λx.(NP (λy.(VT x y))) 
       CN   CN "that" VP           λx.((CN x) ∧ (VP x)) 
       S    NP VP                  (NP VP)                            NP = VP → S
 
-}

open import TTCore

t = Set     -- тип формул / пропозиций
S = t

VP = e → S
CN = e → S           -- CN -- скрытый глагол: "быть ..."  (связка)

VI = e → S

NP = VP → S

DET = CN → NP


a : DET 
a P Q = Σ[ x ∈ e ] P x × Q x      

some = a

every : DET
every P Q = ∀ (x : e) → (P x → Q x)

no : DET 
no P Q = ∀ (x : e) → (P x → ¬ Q x)


postulate
  man   : CN
  runs  : VI
  sings : VI

s1 = a man runs

-- Проверка смысла выражений: C-c C-n.
-- Проверьте s1.

_ : s1 ≡ (Σ[ x ∈ e ] Σ[ p ∈ man x ] runs x)
_ = refl


a-man : NP
a-man = a man

s2 = a-man runs

-- Проверьте s2

_ : s1 ≡ s2
_ = refl


s2' = every man runs

_ : s2' ≡ ∀ (x : e) → man x → runs x
_ = refl



postulate AlicePN : e   -- Alice как PN, т.е. выражение, обозначающее индивида

np : e → NP
np x vp = vp x

Alice = np AlicePN   -- Alice, используемое как NP, Alice = λ vp → vp Alice-e

s0 = Alice runs

_ : s0 ≡ runs AlicePN
_ = refl


VT = e → e → S       -- = NP → VP ?

postulate _loves_ : VT

vp-nptv : NP → VT → VP
vp-nptv np tv = λ x → np (λ y → tv x y)

loves-Alice : VP
loves-Alice = vp-nptv Alice _loves_

-- Alice-loves = λ x → Alice-e loves x,  т.е. Alice-loves x = Alice-e loves x


-- относительные конструкции

_that_ : CN → VP → CN
cn that vp = λ x → cn x × vp x


man-that-runs = man that runs                  -- CN

a-man-that-runs = a man-that-runs              -- NP

s3 = a-man-that-runs sings

_ : s3 ≡ Σ e (λ x → Σ (Σ (man x) (λ _ → runs x)) (λ _ → sings x))
_ = refl

-- то же в других обозначениях:
_ : s3 ≡ (Σ[ x ∈ e ] (Σ[ _ ∈ (Σ[ _ ∈ man x ] (runs x)) ] sings x))
_ = refl

-- учтём независимые типы
_ : s3 ≡ (Σ[ x ∈ e ] ((man x × runs x) × sings x))
_ = refl



-- From Montague's "The proper treatment...", p.253 ssq:
-- "every man loves a woman such that she loves him"

postulate
  woman : CN

loves-z : e → VP
loves-z = λ z x → x loves z 

woman-that-loves-z : e → CN
woman-that-loves-z = λ z → woman that (loves-z z)

a-woman-that-loves-z : e → NP
a-woman-that-loves-z = λ z → a (woman-that-loves-z z)

-- определяем предикат, необходимый для "every man ..."
loves-a-woman-that-loves-x : e → t
loves-a-woman-that-loves-x = λ x → (a-woman-that-loves-z x) (λ y → x loves y)

s5 = every man loves-a-woman-that-loves-x 


_ : s5 ≡ ∀ x → man x → Σ e (λ w → Σ (Σ (woman w) (λ _ → w loves x)) (λ _ → x loves w))
_ = refl

-- другая запись
_ : s5 ≡ ∀ x → man x → Σ[ w ∈ e ] (Σ[ _ ∈ (Σ[ _ ∈ woman w ] (w loves x)) ] (x loves w))
_ = refl

-- ещё одна запись
_ : s5 ≡ ∀ x → man x → Σ[ w ∈ e ] ((woman w × (w loves x)) × (x loves w))
_ = refl
