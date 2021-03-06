-- Montague semantics

-- https://en.wikipedia.org/wiki/Montague_grammar
-- https://plato.stanford.edu/entries/montague-semantics/


module Montague where

module m1 where

  postulate
    t : Set   -- термы / объекты
  
  f = Set     -- тип формул / пропозиций
    
  S   = f                          -- Sentence / предложение
  VP  = t → f                      -- Verb phrase / глагольная группа
  NP  = (t → f) → f                -- Noun phrase / именная группа
  CN  = t → f                      -- Common noun / имя нарицательное
  DET = (t → f) → ((t → f) → f)    -- Determiner 
  TV  = t → (t → f)                -- Transitive verb / транзитивный глагол 
  
  
  -- CN -- скрытый глагол: "быть ..."  (связка)
  
  
  
  -- Примеры
  
  postulate
    Alex : t     -- не вполне корректно,
                 -- у Монтегю собственные имена формализуются иначе
    runs : VP
  
  _ : S
  _ = runs Alex
  
  
  postulate
    man : CN
    the : DET
  
  
  _ : NP
  _ = the man
  
  
  _ : S
  _ = (the man) runs
  
  
  postulate
    _loves_ : TV
    Mary    : t
  
  
  _ : S
  _ = Mary loves Alex
  
  
  _ : VP
  _ = _loves_ Mary
  
  _ : S
  _ = (the man) (_loves_ Mary)   --  the man loves Mary ? Or the other way around?
  
  
  _ : S
  _ = (the man) (Mary loves_) 
  



-- Семантика
-- =========

{---- Семантика по Монтегю: язык первого порядка.

       S    NP VP             (NP VP)
       NP   name              λP. (P name) 
       NP   DET CN            (DET CN)
       NP   DET RCN           (DET RCN) 
       DET  "some"            λP.λQ.∃x ((P x) ∧ (Q x)) 
       DET  "a"               λP.λQ.∃x ((P x) ∧ (Q x)) 
       DET  "every"           λP.λQ.∀x ((P x) → (Q x)) 
       DET  "no"              λP.λQ.∀x ((P x) → (¬ (Q x))) 
       VP   intransverb       λx.intransverb (x) 
       VP   TV NP             λx.(NP (λy.(TV y x))) 
       TV   transverb         λx.λy.transverb (x , y) 
       RCN  CN "that" VP      λx.((CN x) ∧ (VP x)) 
       RCN  CN "that" NP TV   λx.((CN x) ∧ (NP (λy.(TV y x)))) 
       CN   predicate         λx.predicate (x) 
-}

open import TTCore

postulate
  t : Set   -- термы / объекты

f = Set     -- тип формул / пропозиций

CN = t → f
VP = t → f

postulate
  man : CN
  runs : VP
  sings : VP

DET = (t → f) → ((t → f) → f)

a : DET 
a P Q = Σ[ x ∈ t ] P x × Q x

some = a

every : DET
every P Q = ∀ (x : t) → (P x → Q x)

no : DET 
no P Q = ∀ (x : t) → (P x → ¬ Q x)

s1 = a man runs

-- Проверка смысла выражений: C-c C-n


NP = (t → f) → f

a-man : NP
a-man = a man

s2 = a-man runs

_ : s1 ≡ s2
_ = refl



postulate Alice : t   -- Alice как объект

np : t → NP
np x vp = vp x

np-Alice = np Alice   -- Alice, используемое как NP

s0 = np-Alice runs

np-det : DET → CN → NP
np-det det cn = det cn

a-man' : NP
a-man' = np-det a man


TV = t → t → f

postulate _loves_ : TV

vp-nptv : NP → TV → VP
vp-nptv np tv = λ x → np (λ y → tv y x)

Alice-loves = vp-nptv np-Alice _loves_

-- Alice-loves = λ x → Alice loves x,  т.е. Alice-loves x = Alice loves x


RCN = t → f

_that_ : CN → VP → RCN
cn that vp = λ x → cn x × vp x

np-detr : DET → RCN → NP
np-detr det rcn = det rcn

man-that-runs = man that runs

a-man-that-runs = np-detr a man-that-runs

a-man-that-runs-sings = a-man-that-runs sings

-- a-man-that-runs-sings = Σ t (λ x → Σ (Σ (man x) (λ _ → runs x)) (λ _ → sings x))


cn-tv : CN → NP → TV → RCN
cn-tv cn np tv = λ x → cn x × (np (λ y → tv y x))


S = f
s : NP → VP → S
s np vp = np vp

s3 = s a-man-that-runs sings

_ : s3 ≡ a-man-that-runs-sings
_ = refl



s4 = every man runs


