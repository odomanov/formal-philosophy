-- Абстрактный синтаксис. 
-- Упрощённый вариант Ranta's Grammatical Framework.


module AbstractSyntax where

data Tense : Set where TPres TPast TFut : Tense

data A    : Set where small warm : A
data AdA  : Set where very : AdA
data AdV  : Set where always : AdV -- directly attached to verbs
data Conj : Set where and or : Conj
data Det  : Set where a every the this these that those : Det
data N    : Set where man banana door : N
data PN   : Set where John Mary Bill : PN
data Pol  : Set where PPos PNeg : Pol
data Prep : Set where above after at : Prep
data Pron : Set where I she he we : Pron
data V    : Set where run : V
data V2   : Set where love : V2


data AP : Set where             -- Adjective Phrase
  PositA : A → AP
  AdAP   : AdA → AP → AP        -- very big

data Adv  : Set
data CN   : Set
data Comp : Set
data NP   : Set
data VP   : Set

data CN where
  UseN   : N → CN
  AdjCN  : AP → CN  → CN    -- big house
  AdvCN  : CN → Adv → CN    -- house on the hill
  PossNP : CN → NP → CN     -- house of Paris, house of mine
  PartNP : CN → NP → CN     -- glass of wine

data NP where
  DetCN   : Det → CN → NP    -- the man
  UsePN   : PN → NP          -- John
  UsePron : Pron → NP        -- he
  MassNP  : CN → NP

data VP where
  UseV      : V → VP
  AdvVP     : VP → Adv → VP         -- sleep here
  AdVVP     : AdV → VP → VP         -- always sleep
  UseCopula : VP                    -- be
  UseComp   : Comp → VP             -- be warm

data Comp where
  CompAP  : AP  → Comp             -- (be) small
  CompNP  : NP  → Comp             -- (be) the man
  CompAdv : Adv → Comp             -- (be) here
  CompCN  : CN  → Comp             -- (be) a man/men

data Adv where
  here : Adv
  PositAdvAdj : A → Adv                 -- warmly
  PrepNP      : Prep → NP → Adv         -- in the house

data Cl : Set where
  PredVP : NP → VP → Cl

data S : Set where
  UseCl : Tense → Pol → Cl  → S      -- Clause with tense and polarity
  





module Examples where  --------------------------------------------

  -- a man will run
  s1 : S
  s1 = UseCl TFut PPos
                  (PredVP
                    (DetCN a
                           (UseN man))
                    (UseV run))

  -- a man is at the door
  s2 : S
  s2 = UseCl TPres
             PPos
             (PredVP (DetCN a (UseN man))
                     (AdvVP UseCopula (PrepNP at
                                              (DetCN the (UseN door)))))
