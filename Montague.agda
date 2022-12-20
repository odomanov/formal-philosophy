-- Montague semantics

-- https://en.wikipedia.org/wiki/Montague_grammar
-- https://plato.stanford.edu/entries/montague-semantics/


module Montague (e : Set) where         -- e = объекты / тип объектов

{---- Семантика по Монтегю на языке логики предикатов.
      Словам (точнее, грамматическим категориям) соответствуют некоторые функции.
      Семантика определяет эти функции.

       CN   predicate              λx.predicate (x) 
       NP   DET CN                 (DET CN)                           DET = CN → NP
       NP   DET RCN                (DET RCN) 
       NP   name                   λP. (P name)                       NP = P → S
       DET  "some"                 λP.λQ.∃x ((P x) ∧ (Q x))           S = DET p q
       DET  "a"                    λP.λQ.∃x ((P x) ∧ (Q x)) 
       DET  "every"                λP.λQ.∀x ((P x) → (Q x)) 
       DET  "no"                   λP.λQ.∀x ((P x) → (¬ (Q x))) 
       VI   intransverb            λx.intransverb (x)
       VT   transverb              λx.λy.transverb (x , y) 
       VP   VI                                                        VP = VI
       VP   VT NP                  λx.(NP (λy.(VT x y))) 
       RCN  CN "that" VP           λx.((CN x) ∧ (VP x)) 
       RCN  CN "that" NP VT        λx.((CN x) ∧ (NP (λy.(VT y x)))) 
       S    NP VP                  (NP VP)                            NP = VP → S
 
-}

open import TTCore

t = Set     -- тип формул / пропозиций

VP = e → t
CN = e → t           -- CN -- скрытый глагол: "быть ..."  (связка)

VI = e → t

NP = (e → t) → t

DET = (e → t) → ((e → t) → t)     -- CN → NP

-- проверим, что DET ≡ CN → NP
_ : DET ≡ (CN → NP)
_ = refl 


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


a-man : NP
a-man = a man

s2 = a-man runs

-- Проверьте s2

_ : s1 ≡ s2
_ = refl


s2' = every man runs

_ : s2' ≡ ∀ (x : e) → man x → runs x
_ = refl



postulate Alice-e : e   -- Alice как объект  (точнее, должно быть PN, я немного упрощаю)

np : e → NP
np x vp = vp x

Alice = np Alice-e   -- Alice, используемое как NP, Alice = λ vp → vp Alice-e

s0 = Alice runs

_ : s0 ≡ runs Alice-e
_ = refl


VT = e → e → t

postulate _loves_ : VT

vp-nptv : NP → VT → VP
vp-nptv np tv = λ x → np (λ y → tv x y)

loves-Alice : VP
loves-Alice = vp-nptv Alice _loves_

-- Alice-loves = λ x → Alice-e loves x,  т.е. Alice-loves x = Alice-e loves x


RCN = e → t

-- проверим, что DET ≡ RCN → NP
_ : DET ≡ (RCN → NP)
_ = refl


_that_ : CN → VP → RCN
cn that vp = λ x → cn x × vp x


man-that-runs = man that runs                  -- RCN

a-man-that-runs = a man-that-runs              -- NP

s3 = a-man-that-runs sings

_ : s3 ≡ Σ e (λ x → Σ (Σ (man x) (λ _ → runs x)) (λ _ → sings x))
_ = refl



-- From Montague's "The proper treatment...", p.253 ssq:
-- "every man loves a woman such that she loves him"

postulate
  woman : CN

loves-z : e → VP
loves-z = λ z x → x loves z 

woman-that-loves-z : e → RCN
woman-that-loves-z = λ z → woman that (loves-z z)

a-woman-that-loves-z : e → NP
a-woman-that-loves-z = λ z → a (woman-that-loves-z z)

loves-a-woman-that-loves-x : VP
loves-a-woman-that-loves-x = λ x → (a-woman-that-loves-z x) (λ y → x loves y)

s5 = every man loves-a-woman-that-loves-x 


_ : s5 ≡ ∀ x → man x → Σ e (λ w → Σ (Σ (woman w) (λ _ → w loves x)) (λ _ → x loves w))
_ = refl

-- другая запись
_ : s5 ≡ ∀ x → man x → Σ[ w ∈ e ] (Σ[ _ ∈ (Σ[ _ ∈ woman w ] (w loves x)) ] (x loves w))
_ = refl
