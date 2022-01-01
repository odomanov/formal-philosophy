-- Montague semantics

-- https://en.wikipedia.org/wiki/Montague_grammar
-- https://plato.stanford.edu/entries/montague-semantics/


module Montague where

module m1 where

-- Синтаксис
-- =========

  postulate
    e : Set   -- термы / объекты
  
  t = Set     -- тип формул / пропозиций
    
  S   = t                          -- Sentence / предложение
  VP  = e → t                      -- Verb phrase / глагольная группа,  E → S
  NP  = (e → t) → t                -- Noun phrase / именная группа,  VP → S
  CN  = e → t                      -- Common noun / имя нарицательное, E → S
  DET = (e → t) → ((e → t) → t)    -- Determiner,  CN → NP
  TV  = e → (e → t)                -- Transitive verb / транзитивный глагол, E → VP
  
  
  -- CN -- скрытый глагол: "быть ..."  (связка)
  
  
  
  -- Примеры
  
  postulate
    Alex : e     -- не вполне корректно,
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
    Mary    : e
  
  
  _ : S
  _ = Mary loves Alex
  
  
  _ : VP
  _ = _loves_ Mary
  
  _ : S
  _ = (the man) (_loves_ Mary)   --  the man loves Mary ? Or the other way around?
  
  
  _ : S
  _ = (the man) (Mary loves_) 
  


  -- From Montague's "The proper treatment...":
  -- every man loves a woman such that she loves him

  ST = CN → S → CN      -- sn such that s

  postulate
    woman : CN
    _such-that_ : ST
    every : DET
    a : DET
    him she : e

  _ : NP
  _ = every man

  _ : S
  _ = she loves him
  
  -- _ : S
  -- _ = (every man) loves ((a woman) such-that (she loves him))


-- Семантика
-- =========

-- Определения выше позволяют нам трансформировать языковые выражения в выражения λ-исчисления.
-- Словам в них соответствуют некоторые функции. Семантика определяет эти функции.

{---- Семантика по Монтегю: язык логики предикатов.

       S    NP VP                  (NP VP)
       NP   name                   λP. (P name) 
       NP   DET CN                 (DET CN)
       NP   DET RCN                (DET RCN) 
       DET  "some"                 λP.λQ.∃x ((P x) ∧ (Q x)) 
       DET  "a"                    λP.λQ.∃x ((P x) ∧ (Q x)) 
       DET  "every"                λP.λQ.∀x ((P x) → (Q x)) 
       DET  "no"                   λP.λQ.∀x ((P x) → (¬ (Q x))) 
       VP   intransverb            λx.intransverb (x) 
       VP   TV NP                  λx.(NP (λy.(TV y x))) 
       TV   transverb              λx.λy.transverb (x , y) 
       RCN  CN "such that" VP      λx.((CN x) ∧ (VP x)) 
       RCN  CN "such that" NP TV   λx.((CN x) ∧ (NP (λy.(TV y x)))) 
       CN   predicate              λx.predicate (x) 
-}

open import TTCore

postulate
  e : Set   -- термы / объекты

t = Set     -- тип формул / пропозиций

CN = e → t
VP = e → t

postulate
  man : CN
  runs : VP
  sings : VP

DET = (e → t) → ((e → t) → t)     -- CN → NP

a : DET 
a P Q = Σ[ x ∈ e ] P x × Q x    -- Σ A B      B : A → Set

some = a

every : DET
every P Q = ∀ (x : e) → (P x → Q x)

no : DET 
no P Q = ∀ (x : e) → (P x → ¬ Q x)

s1 = a man runs

-- Проверка смысла выражений: C-c C-n


NP = (e → t) → t

_ : DET ≡ CN → NP
_ = λ _ z → (x : e) → z x

a-man : NP
a-man = a man

s2 = a-man runs

_ : s1 ≡ s2
_ = refl



postulate Alice : e   -- Alice как объект

np : e → NP
np x vp = vp x

np-Alice = np Alice   -- Alice, используемое как NP

s0 = np-Alice runs

np-det : DET → CN → NP
np-det det cn = det cn

a-man' : NP
a-man' = np-det a man


TV = e → e → t

postulate _loves_ : TV

vp-nptv : NP → TV → VP
vp-nptv np tv = λ x → np (λ y → tv y x)

Alice-loves = vp-nptv np-Alice _loves_

-- Alice-loves = λ x → Alice loves x,  т.е. Alice-loves x = Alice loves x


RCN = e → t

_that_ : CN → VP → RCN
cn that vp = λ x → cn x × vp x

np-detr : DET → RCN → NP
np-detr det rcn = det rcn

man-that-runs = man that runs    -- RCN

a-man-that-runs = np-detr a man-that-runs   -- NP

a-man-that-runs-sings = a-man-that-runs sings  -- S

-- a-man-that-runs-sings = Σ e (λ x → Σ (Σ (man x) (λ _ → runs x)) (λ _ → sings x))


cn-tv : CN → NP → TV → RCN
cn-tv cn np tv = λ x → cn x × (np (λ y → tv y x))


S = t
s : NP → VP → S
s np vp = np vp

s3 = s a-man-that-runs sings

_ : s3 ≡ a-man-that-runs-sings
_ = refl



s4 = every man runs


