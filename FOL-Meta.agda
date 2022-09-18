-- Agda как метаязык для языка первого порядка.
-- TODO: правила вывода, soundness, completeness, подстановка


open import Data.Bool renaming (_∧_ to _∧ᵇ_ ; _∨_ to _∨ᵇ_; not to ¬ᵇ)
open import Data.Nat using (ℕ)


module FOL-Meta (Var Func Pred : Set)
                (_≈_ : Var → Var → Bool)
                (FArity : Func → ℕ) (PArity : Pred → ℕ) where

open import Data.List
open import Data.Vec renaming ([] to []v; _∷_ to _∷v_; map to mapv)
open import Relation.Binary.PropositionalEquality

data Term : Set where
  var  : Var → Term
  func : (f : Func) → Vec Term (FArity f) → Term
  

-- Formulas
data Frm : Set where
  pred : (p : Pred) → Vec Term (PArity p) → Frm
  _==_ : Term → Term → Frm
  ¬_ : Frm → Frm
  _∧_ : Frm → Frm → Frm
  _∨_ : Frm → Frm → Frm
  _⇒_ : Frm → Frm → Frm
  All_=>_ : Var → Frm → Frm
  Ex_=>_ : Var → Frm → Frm


-- Model

record Model : Set1 where
  field
    Object : Set
    ObjEq : Object → Object → Bool
    Domain : List Object
    vfunc : (f : Func) → Vec Object (FArity f) → Object  
    vpred : (p : Pred) → Vec Object (PArity p) → Bool

open Model

-- x-variant of ρ
ρₓ : {m : Model} → (Var → Object m) → Var → Object m → (Var → Object m)
ρₓ ρ x o y = if x ≈ y then o else ρ x

vterm : {m : Model} → (Var → Object m) → Term → Object m
vvec  : ∀ {n} {m : Model} → (Var → Object m) → Vec Term n → Vec (Object m) n

-- значение последовательности переменных при валюации ρ 
vvec         _    []v = []v
vvec {m = m} ρ (x ∷v xs) = vterm {m} ρ x ∷v vvec {m = m} ρ xs  -- это map
-- vvec {m = m} ρ xs = mapv (vterm {m} ρ) xs

-- значение терма при валюации ρ 
vterm     ρ (var x) = ρ x
vterm {m} ρ (func f vt) = (vfunc m) f (vvec {m = m} ρ vt)


-- Evaluation

{-# TERMINATING #-}
_,_⊨_ : (m : Model) → (Var → Object m) → Frm → Bool
m , ρ ⊨ (pred p vt) = (vpred m) p (vvec {_} {m} ρ vt)
m , ρ ⊨ (s == r)    = (ObjEq m) (vterm {m} ρ s) (vterm {m} ρ r)
m , ρ ⊨ (¬ s)       = ¬ᵇ (m , ρ ⊨ s)
m , ρ ⊨ (s ∧ r)     = (m , ρ ⊨ s) ∧ᵇ (m , ρ ⊨ r)
m , ρ ⊨ (s ∨ r)     = (m , ρ ⊨ s) ∨ᵇ (m , ρ ⊨ r)
m , ρ ⊨ (s ⇒ r)     =  m , ρ ⊨ ((¬ s) ∨ r)
m , ρ ⊨ (All x => s) = ev-all (Domain m) s
  where
  ev-all : List (Object m) → Frm → Bool
  ev-all [] F = true
  ev-all (y ∷ ys) F = (m , (ρₓ {m} ρ x y) ⊨ F) ∧ᵇ (ev-all ys F)
m , ρ ⊨ (Ex x => s) = ev-ex (Domain m) s
  where
  ev-ex : List (Object m) → Frm → Bool
  ev-ex [] F = false
  ev-ex (y ∷ ys) F = (m , (ρₓ {m} ρ x y) ⊨ F) ∨ᵇ (ev-ex ys F)
  

