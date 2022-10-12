-- Agda как метаязык для модальной логики
-- TODO: правила вывода, soundness, completeness, подстановка


open import Data.Bool renaming (_∧_ to _∧ᵇ_ ; _∨_ to _∨ᵇ_; not to ¬ᵇ)
open import Data.Nat using (ℕ)


module FOLModal-Meta (Var Func Pred : Set)
                     (_≈_ : Var → Var → Bool)
                     (FArity : Func → ℕ) (PArity : Pred → ℕ) where

open import Data.Empty
open import Data.List
open import Data.Product
open import Data.Unit
open import Data.Vec renaming ([] to []v; _∷_ to _∷v_)
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
  ◇_ : Frm → Frm
  □_ : Frm → Frm
  


-- Model

record Model : Set1 where
  field
    World  : Set
    AccRel : World → World → Bool
    WorldL : List World
    Object : Set  -- full domain
    ObjEq  : Object → Object → Bool
    Domain : World → List Object
    vfunc  : World → (f : Func) → Vec Object (FArity f) → Object  
    vpred  : World → (p : Pred) → Vec Object (PArity p) → Bool

open Model

-- x-variant of ρ
ρₓ : {m : Model} → (Var → Object m) → Var → Object m → (Var → Object m)
ρₓ ρ x o y = if x ≈ y then o else ρ x

vterm : {m : Model} → World m → (Var → Object m) → Term → Object m
vvec  : ∀ {n} {m : Model} → World m → (Var → Object m) → Vec Term n → Vec (Object m) n

-- значение последовательности переменных при валюации ρ 
vvec         _ _    []v = []v
vvec {m = m} w ρ (x ∷v xs) = vterm {m} w ρ x ∷v vvec {m = m} w ρ xs

-- значение терма при валюации ρ 
vterm     _ ρ (var x) = ρ x
vterm {m} w ρ (func f vt) = (vfunc m) w f (vvec {m = m} w ρ vt)

Acc : (m : Model) → (w : World m) → List (World m)
Acc m w = Acc' (WorldL m)
  where
  Acc' : List (World m) → List (World m)
  Acc' [] = []
  Acc' (x ∷ xs) = if AccRel m w x then x ∷ Acc' xs else Acc' xs 

-- Evaluation

{-# TERMINATING #-}
_,_,_⊨_ : (m : Model) → World m → (Var → Object m) → Frm → Bool
m , w , ρ ⊨ (pred p vt) = (vpred m w) p (vvec {_} {m} w ρ vt)
m , w , ρ ⊨ (s == r)    = (ObjEq m) (vterm {m} w ρ s) (vterm {m} w ρ r)
m , w , ρ ⊨ (¬ s)       = ¬ᵇ (m , w , ρ ⊨ s)
m , w , ρ ⊨ (s ∧ r)     = (m , w , ρ ⊨ s) ∧ᵇ (m , w , ρ ⊨ r)
m , w , ρ ⊨ (s ∨ r)     = (m , w , ρ ⊨ s) ∨ᵇ (m , w , ρ ⊨ r)
m , w , ρ ⊨ (s ⇒ r)     =  m , w , ρ ⊨ ((¬ s) ∨ r)
m , w , ρ ⊨ (All x => s) = ev-all (Domain m w) s where
  ev-all : List (Object m) → Frm → Bool
  ev-all [] F = true
  ev-all (y ∷ ys) F = (m , w , (ρₓ {m} ρ x y) ⊨ F) ∧ᵇ (ev-all ys F)
m , w , ρ ⊨ (Ex x => s) = ev-ex (Domain m w) s where
  ev-ex : List (Object m) → Frm → Bool
  ev-ex [] F = false
  ev-ex (y ∷ ys) F = (m , w , (ρₓ {m} ρ x y) ⊨ F) ∨ᵇ (ev-ex ys F)
m , w , ρ ⊨ (□ s) = w-all (Acc m w) s where
  w-all : List (World m) → Frm → Bool
  w-all [] s = true
  w-all (x ∷ xs) s = (m , x , ρ ⊨ s) ∧ᵇ w-all xs s
m , w , ρ ⊨ (◇ s) = w-ex (Acc m w) s where
  w-ex : List (World m) → Frm → Bool
  w-ex [] s = false
  w-ex (x ∷ xs) s = (m , x , ρ ⊨ s) ∨ᵇ w-ex xs s 

  

