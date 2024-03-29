-- Agda как метаязык для модальной логики
-- TODO: правила вывода, soundness, completeness, подстановка


open import Data.Bool renaming (_∧_ to _∧ᵇ_ ; _∨_ to _∨ᵇ_; not to ¬ᵇ)
open import Data.Nat using (ℕ)


module FOLModal-Meta (Var Func Pred : Set)         -- symbols / names
                     (_≈_ : Var → Var → Bool)
                     (FArity : Func → ℕ)
                     (PArity : Pred → ℕ) where

open import Data.Empty
open import Data.List
open import Data.Product
open import Data.Unit
open import Data.Vec renaming ([] to []v; _∷_ to _∷v_)
open import Relation.Binary.PropositionalEquality


--==  Syntax  ==--

data Term : Set where
  var  : Var → Term
  func : (f : Func) → Vec Term (FArity f) → Term
  
-- Formulas
data Formula : Set where
  pred : (p : Pred) → Vec Term (PArity p) → Formula
  _==_ : Term → Term → Formula
  ¬_   : Formula → Formula
  _∧_  : Formula → Formula → Formula
  _∨_  : Formula → Formula → Formula
  _⇒_  : Formula → Formula → Formula
  All_=>_ : Var → Formula → Formula
  Ex_=>_  : Var → Formula → Formula
  ◇_ : Formula → Formula
  □_ : Formula → Formula
  


--==  Semantics  ==--

-- Model

record Model : Set1 where
  field
    World  : Set
    Worlds : List World
    AccRel : World → World → Bool
    Object : Set                             -- full domain
    ObjEq  : Object → Object → Bool
    Domain : World → List Object             -- domain for w
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

-- Миры, достижимые из w (в модели m)
Acc : (m : Model) → (w : World m) → List (World m)
Acc m w = Acc' (Worlds m)
  where
  Acc' : List (World m) → List (World m)
  Acc' [] = []
  Acc' (x ∷ xs) = if AccRel m w x then x ∷ Acc' xs else Acc' xs 

-- Evaluation

{-# TERMINATING #-}
_,_,_⊨_ : (m : Model) → World m → (Var → Object m) → Formula → Bool
m , w , ρ ⊨ (pred p vt) = (vpred m w) p (vvec {_} {m} w ρ vt)
m , w , ρ ⊨ (s == r)    = (ObjEq m) (vterm {m} w ρ s) (vterm {m} w ρ r)
m , w , ρ ⊨ (¬ s)       = w-not (Acc m w) s
  where
  w-not : List (World m) → Formula → Bool
  w-not [] s = true
  w-not (w' ∷ ws) s = ¬ᵇ (m , w' , ρ ⊨ s) ∧ᵇ w-not ws s 
m , w , ρ ⊨ (s ∧ r)     = (m , w , ρ ⊨ s) ∧ᵇ (m , w , ρ ⊨ r)
m , w , ρ ⊨ (s ∨ r)     = (m , w , ρ ⊨ s) ∨ᵇ (m , w , ρ ⊨ r)
m , w , ρ ⊨ (s ⇒ r)     =  m , w , ρ ⊨ ((¬ s) ∨ r)
m , w , ρ ⊨ (All x => s) = ev-all (Domain m w) s
  where
  ev-all : List (Object m) → Formula → Bool
  ev-all [] F = true
  ev-all (y ∷ ys) F = (m , w , (ρₓ {m} ρ x y) ⊨ F) ∧ᵇ (ev-all ys F)
m , w , ρ ⊨ (Ex x => s) = ev-ex (Domain m w) s
  where
  ev-ex : List (Object m) → Formula → Bool
  ev-ex [] F = false
  ev-ex (y ∷ ys) F = (m , w , (ρₓ {m} ρ x y) ⊨ F) ∨ᵇ (ev-ex ys F)
m , w , ρ ⊨ (□ s) = w-all (Acc m w) s
  where
  w-all : List (World m) → Formula → Bool
  w-all [] s = true
  w-all (x ∷ xs) s = (m , x , ρ ⊨ s) ∧ᵇ w-all xs s
m , w , ρ ⊨ (◇ s) = w-ex (Acc m w) s
  where
  w-ex : List (World m) → Formula → Bool
  w-ex [] s = false
  w-ex (x ∷ xs) s = (m , x , ρ ⊨ s) ∨ᵇ w-ex xs s 

