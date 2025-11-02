-- Семантика Монтегю / Montague semantics

-- https://en.wikipedia.org/wiki/Montague_grammar
-- https://plato.stanford.edu/entries/montague-semantics/


-- e, t это типы выражений языка.
-- e обозначает тип индивидов, t -- тип пропозиций или формул.

-- class MontagueOntology where
--   type : Type

namespace Montague
-- variable [mo : MontagueOntology]

/- -- Семантика по Монтегю на языке логики предикатов.
      Словам (точнее, грамматическим категориям) соответствуют некоторые функции.

       CN   predicate              λx.P x
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

-/

-- abbrev e := mo.type
abbrev e := Type
abbrev t := Prop     -- тип формул / пропозиций
abbrev S := t

abbrev VP := e → S
abbrev CN := e → S           -- CN -- скрытый глагол: "быть ..."  (связка)

abbrev VI := e → S

-- У Монтегю VI определяется как t/e, а CN --- как t//e.
-- Кроме того, он не различает VI и VP.

abbrev NP := VP → S

abbrev DET := CN → NP


def a : DET := λ P Q => ∃ x : e, P x ∧ Q x

def some := a

def every : DET := λ P Q => ∀ x : e, P x → Q x

def no : DET := λ P Q => ∀ x : e, P x → ¬ Q x


axiom man   : CN
axiom runs  : VI
axiom sings : VI

def s1 : S := a man runs

example : s1 = ∃ x : e, man x ∧ runs x := rfl

def a_man : NP := a man

def s2 : S := a_man runs

-- Проверьте s2

example : s1 = s2 := rfl


def s2' := every man runs

example : s2' = ∀ x : e, man x → runs x := rfl



axiom AlicePN : e   -- Alice как PN, т.е. выражение, обозначающее индивида

def np : e → NP := λ x vp => vp x

abbrev Alice := np AlicePN   -- Alice, используемое как NP, Alice = λ vp → vp Alice-e

abbrev s0 := Alice runs

example : s0 = runs AlicePN := rfl


def VT := e → e → S       -- = NP → VP ?

axiom loves : VT

notation x:arg " loves " y:arg => loves x y

def vp_nptv : NP → VT → VP := λ np tv x => np (tv x ·)

def loves_Alice : VP := vp_nptv Alice (· loves ·)

-- Alice-loves = λ x → Alice-e loves x,  т.е. Alice-loves x = Alice-e loves x


-- относительные конструкции

abbrev that : CN → VP → CN := λ cn vp x => cn x ∧ vp x

notation x:arg " that " y:arg => that x y

abbrev man_that_runs := man that runs                  -- CN

abbrev a_man_that_runs := a man_that_runs              -- NP

abbrev s3 := a_man_that_runs sings

example : s3 = ∃ x : e, (man x ∧ runs x) ∧ sings x := rfl



-- From Montague's "The proper treatment...", p.253 ssq:
-- "every man loves a woman such that she loves him"

axiom woman : CN

def loves_z : e → VP := λ z x => x loves z

def woman_that_loves_z : e → CN := λ z => woman that (loves_z z)

def a_woman_that_loves_z : e → NP := λ z => a (woman_that_loves_z z)

-- определяем предикат, необходимый для "every man ..."
def loves_a_woman_that_loves_x : e → t :=
  λ x => (a_woman_that_loves_z x) (λ y => x loves y)

def s5 := every man loves_a_woman_that_loves_x

example : s5 = ∀ x, man x → ∃ w : e, (woman w ∧ w loves x) ∧ (x loves w)
  := rfl
