-- Мы сразу строим типизированное исчисление.  Нетипизированное получается
-- из него при отграничении одним типом.

-- В этом файле термы индексируются типами.  Поэтому они всегда корректны.

-- TODO: добавить вычисления в самом λ-исчислении (редукцию).

module LambdaCalculus2-Meta where

open import Data.Empty using (⊥)
open import Data.Maybe 
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc; #_; fromℕ; toℕ)
open import Data.Product using (Σ; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable.Core using (fromWitness)


module Syntax (TypeNames : Set) (_≡d_ : (x y : TypeNames) → Dec (x ≡ y)) where

  data Type : Set where
    *   : TypeNames → Type
    _⇒_ : Type → Type → Type 

  infixr 3 lam_⇒_
  infixr 4 _∙_
  infixl 5 _✦_

  -- n -- длина контекста (количество переменных)
  data Context : ℕ → Set where
    ∅   : Context zero
    _✦_ : ∀ {n} → Context n → Type → Context (suc n)
  
  lookup : ∀ {n} → Fin n → Context n → Type
  lookup zero (_ ✦ x) = x
  lookup (suc i) (xs ✦ _) = lookup i xs

  -- правила вывода содержатся в термах.
  -- поэтому термы всегда корректны
  data Term {n} (Γ : Context n) : Type → Set where
    var    : (i : Fin n) → Term Γ (lookup i Γ)
    _∙_    : ∀ {A B} → Term Γ (A ⇒ B) → Term Γ A → Term Γ B
    lam_⇒_ : ∀ A {B} → Term (Γ ✦ A) B → Term Γ (A ⇒ B)

  -- a : Term Γ A это суждение Γ ⊢ a : A
  

  -- Синтаксическая выводимость суждения t : A
  data _⊢_⦂_ {n} (Γ : Context n) : ∀ {A} → Term Γ A → Type → Set where
    prf : ∀ {A} {t : Term Γ A} → Γ ⊢ t ⦂ A


  -- Определим разрешимое равенство типов
  _≟_ : (A B : Type) → Dec (A ≡ B)
  * x ≟ * y with x ≡d y
  ... | yes refl = yes refl
  ... | no ¬p = no λ z → ¬p (pp z)
      where
      pp : ∀ {x y} → * x ≡ * y → x ≡ y
      pp refl = refl
  (A ⇒ C) ≟ (B ⇒ D) with A ≟ B | C ≟ D
  ... | yes refl | yes refl = yes refl
  ... | no  ¬p   | _        = no λ z → ¬p (pp z)
      where
      pp : ∀ {A B C D} → A ⇒ C ≡ B ⇒ D → A ≡ B
      pp refl = refl
  ... | _        | no  ¬p   = no λ z → ¬p (pp z)
      where
      pp : ∀ {A B C D} → A ⇒ C ≡ B ⇒ D → C ≡ D
      pp refl = refl
  * x ≟ (A ⇒ B) = no (λ ())
  (A ⇒ B) ≟ * x = no (λ ())
  

  -----------------------------------------------------------------
  -- Другой способ проверки корректности.

  module m where
  
    -- Выражение выглядит как терм, но может не быть корректным.
    data Expr : Set where
      var : ℕ → Expr
      _∙_ : Expr → Expr → Expr
      lam_⇒_ : Type → Expr → Expr
      
    check : ∀ {n} (Γ : Context n) (e : Expr) → Maybe (Σ Type (Term Γ))
    check {n} Γ (var i) with i ℕ.<? n
    ... | yes p = just ((lookup (#_ i {m<n = fromWitness p}) Γ) , var (# i))
    ... | no  _ = nothing
    check Γ (e₁ ∙ e₂) with check Γ e₁ | check Γ e₂
    ... | just ((A ⇒ B) , -e₁) | just (A' , -e₂) with A ≟ A'
    ...                                        | yes refl = just (B , (-e₁ ∙ -e₂))
    ...                                        | no  _ = nothing
    check Γ (e₁ ∙ e₂) | _ | _ = nothing
    check Γ (lam A ⇒ e) with check (Γ ✦ A) e
    ... | just (B , -e) = just ((A ⇒ B) , (lam A ⇒ -e))
    ... | _ = nothing

  -----------------------------------------------------------------

module Semantics (TypeNames : Set)
                 (_≡d_ : (x y : TypeNames) → Dec (x ≡ y))
                 (val : TypeNames → Set) where

  open import Function using (typeOf)
  
  open Syntax TypeNames _≡d_ public

  -- значение выражений для типов (т.е. интерпретируем и вычисляем в Агде)
  TValue : Type → Set
  TValue (* A) = val A 
  TValue (A ⇒ B) = TValue A → TValue B

  -- Env зависит от Γ и соответствует Γ.
  -- Env это модель!
  data Env : ∀ {n} → Context n → Set where
    ∅ : Env ∅
    _✦_ : ∀ {n} {Γ : Context n} {A} → Env Γ → TValue A → Env (Γ ✦ A)

  -- lookup for Env
  _[_] : ∀ {n} {Γ : Context n} → Env Γ → (i : Fin n) → TValue (lookup i Γ) 
  (_ ✦ x) [ zero ] = x
  (E ✦ _) [ suc i ] = E [ i ]

  
  -- Значение терма в окружении Env 
  Value : ∀ {n} {Γ : Context n} {A} → Env Γ → Term Γ A → TValue A
  Value E (var i)     = E [ i ]
  Value E (t₁ ∙ t₂)   = (Value E t₁) (Value E t₂)
  Value E (lam _ ⇒ t) = λ x → Value (E ✦ x) t


  _ : ∀ {n} {Γ : Context n} {A} {E : Env Γ} {t : Term Γ A} → typeOf (Value E t) ≡ TValue A
  _ = refl
  
  -- выполнимость (суждений t ⦂ A) в модели.
  -- ⊩prf означает, что если я посчитаю значение t в модели, то его тип (в модели)
  --   будет равен значению A.
  data _⊩_⦂_ {n} {Γ : Context n} (m : Env Γ) {A} (t : Term Γ A) : Type → Set where
    ⊩prf : m ⊩ t ⦂ A

  -- корректность и полнота тривиальны
  soundness : ∀ {n} {Γ : Context n} {A} {t : Term Γ A} {m : Env Γ} → Γ ⊢ t ⦂ A → m ⊩ t ⦂ A
  soundness prf = ⊩prf 

  completeness : ∀ {n} {Γ : Context n} {A} {t : Term Γ A} {m : Env Γ} → m ⊩ t ⦂ A → Γ ⊢ t ⦂ A
  completeness ⊩prf = prf 



--------  Test

data Names : Set where
  nP nQ nR : Names

_=t_ : (x y : Names) → Dec (x ≡ y)
nP =t nP = yes refl
nQ =t nQ = yes refl
nR =t nR = yes refl
nP =t nQ = no λ () 
nP =t nR = no λ () 
nQ =t nP = no λ () 
nQ =t nR = no λ () 
nR =t nP = no λ () 
nR =t nQ = no λ () 

postulate
  P Q R : Set
  p : P
  q : Q
  r : R

valuation : Names → Set
valuation nP = P
valuation nQ = Q
valuation nR = R

open Semantics Names _=t_ valuation


Γ : Context 3
Γ = ∅ ✦ (* nP) ✦ (* nQ) ✦ (* nR)

E : Env Γ
E = ∅ ✦ p ✦ q ✦ r 

_ : Term Γ _
_ = (lam (* nP) ⇒ var (# 1)) ∙ var (# 2)

_ : Value E (var (# 0)) ≡ r
_ = refl

_ : Value E (var (# 2)) ≡ p
_ = refl

_ : Value ∅ (lam * nP ⇒ (var (# 0))) ≡ λ (x : P) → x 
_ = refl

_ : Value E (lam * nP ⇒ (var (# 2))) ≡ λ (_ : P) → q
_ = refl

_ : Value E (lam * nP ⇒ lam * nR ⇒ (var (# 3))) ≡ λ (x : P) (y : R) → q
_ = refl

_ : Value E ((lam * nP ⇒ (var (# 2))) ∙ (var (# 2))) ≡ q
_ = refl

_ : Value ∅ (lam (* nR ⇒ * nP) ⇒ lam * nR ⇒ (var (# 1)) ∙ (var (# 0)))
          ≡ λ (x : R → P) (y : R) → x y
_ = refl

