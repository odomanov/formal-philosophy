-- Frame Semantics / фреймовая семантика
-- Gawton J.M., Circumstances and Perspective: The Logic of Argument Structure (2008)

namespace Frame

inductive Animate : Type where | «Вася» | «Маша»
inductive Entity : Type where | «книга» | fromAnimate : Animate → Entity
open Animate
open Entity
def cAE : Animate → Entity := Entity.fromAnimate
instance : Coe Animate Entity where
  coe := cAE

structure AgentPatient : Type _ where
  agent : Animate
  patient : Entity
  source : Option Entity := none
  goal : Option Entity := none

structure PossessionTransfer : Type _ where
  donor : Animate
  possession : Entity
  recipient : Animate

def acquisition (pt : PossessionTransfer) : AgentPatient :=
  { agent := pt.recipient,
    patient := pt.possession,
    source := pt.donor }

def donation (pt : PossessionTransfer) : AgentPatient :=
  { agent := pt.donor
    patient := pt.possession
    goal := pt.recipient }

inductive hasGoal : AgentPatient → Type _ where
  | has : (x y : Animate) → (z : Entity) → hasGoal { goal := (some x), agent := y, patient := z }

def «donation⁻¹» (ap : AgentPatient) (hg : hasGoal ap) : PossessionTransfer :=
  { donor := ap.agent
    possession := ap.patient
    recipient := match hg with
      | .has x _ _ => x
    }

-- фрейм двухобъектных переходных глаголов
structure VT2 where
  agent : Animate
  object_dir : Entity
  object_indir : Entity

def give (pt : PossessionTransfer) : VT2 :=
  { agent := pt.donor
    object_dir := pt.possession
    object_indir := pt.recipient  }

def pt1 : PossessionTransfer :=
  { donor := «Маша»
    possession := «книга»
    recipient := «Вася»  }

example : VT2 := give pt1

#check VT2.mk

inductive SPossessionTransfer : PossessionTransfer → Type _ where
| sp1 : SPossessionTransfer pt1

def give' (ap : AgentPatient) (hg : hasGoal ap) : Type :=
  SPossessionTransfer <| «donation⁻¹» ap hg

-- private def type_of {α : Type u} (_ : α) : Type u := α
-- #eval type_of 5

def donation_op (ap : AgentPatient) (p : Σ' x : Animate, some ↑x = ap.goal) : PossessionTransfer :=
  match ap with
  | AgentPatient.mk x y .. =>
    { donor := p.fst
      possession := y
      recipient := x
    }

-- дал что-то кому-то
def give'' (ap : AgentPatient) (p : Σ' x : Animate, some ↑x = ap.goal) : Type :=
  SPossessionTransfer <| donation_op ap p

def give''' (x : Animate) (y : Entity) (z : Animate) : Type :=
  let ap : AgentPatient := { agent := x, patient := y, goal := z}
  give'' ap (by exists z)


def acquisition_op (ap : AgentPatient) (p : Σ' x : Animate, some ↑x = ap.source) : PossessionTransfer :=
  match ap with
  | AgentPatient.mk x y .. =>
    { donor := p.fst
      possession := y
      recipient := x
    }

-- получил что-то откуда-то
def acquire (ap : AgentPatient) (p : Σ' x : Animate, some ↑x = ap.source) : Type :=
  SPossessionTransfer <| acquisition_op ap p

def acquire' (x : Animate) (y : Entity) (z : Animate) : Type :=
  let ap : AgentPatient := { agent := x, patient := y, source := some z}
  acquire ap (by exists z)


inductive Fungible where

structure CommercialTransaction where
  buyer : Animate
  seller : Animate
  money : Fungible
  goods : Entity

def goods_transfer (ct : CommercialTransaction) : PossessionTransfer :=
    { donor := ct.seller
      recipient := ct.buyer
      possession := ct.goods}
