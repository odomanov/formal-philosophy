-- Мы сразу строим типизированное исчисление.  Нетипизированное получается
-- из него при отграничении одним типом.
-- Определяем "пре-термы" и правила вывода, а затем значения только для
--   выводимых термов.

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Nullary using (Dec; yes; no)

module LambdaCalculus-Meta where

open import Data.Empty 
open import Data.Maybe 
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc; #_)
open import Data.Unit using (⊤)

module Syntax (TypeNames : Set) (_≡d_ : (x y : TypeNames) → Dec (x ≡ y)) where

  data Type : Set where
    *   : TypeNames → Type
    _⇒_ : Type → Type → Type 

  -- "пре-термы", могут быть некорректны
  data Term n : Set where
    var : Fin n → Term n
    _∙_ : Term n → Term n → Term n
    _↦_ : Type → Term (suc n) → Term n

  infixr 3 _↦_
  infixr 4 _∙_
  infixl 5 _,_

  -- n -- длина контекста (количество переменных)
  data Context : ℕ → Set where
    ∅   : Context zero
    _,_ : ∀ {n} → Context n → Type → Context (suc n)
  
  lookup : ∀ {n} → Fin n → Context n → Type
  lookup zero (_ , x) = x
  lookup (suc i) (xs , _) = lookup i xs

  -- правила вывода (построения термов)
  data _⊢_⦂_ {n} : Context n → Term n → Type → Set where
    ⊢v : ∀ {Γ i}
       ----------
       → Γ ⊢ (var i) ⦂ lookup i Γ

    ⊢∙ : ∀ {Γ A B f a}
       → Γ ⊢ f ⦂ (A ⇒ B)
       → Γ ⊢ a ⦂ A
       ----------
       → Γ ⊢ f ∙ a ⦂ B

    ⊢⇒ : ∀ {Γ A B b}
       → (Γ , A) ⊢ b ⦂ B
       ----------
       → Γ ⊢ (A ↦ b) ⦂ (A ⇒ B)
  
  -- Конструктор замкнутых термов
  -- Closed : Type → Set
  -- Closed = Term ∅ 

  -- разрешимое равенство типов
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
  
  
  -- type inference
  check : ∀ {n} → Context n → Term n → Maybe Type
  check Γ (var i) = just (lookup i Γ)
  check Γ (t1 ∙ t2) with check Γ t1 | check Γ t2
  ...               | just (A ⇒ B) | just A' with A ≟ A'
  ...                                        | yes _ = just B
  ...                                        | no  _ = nothing
  check Γ (t1 ∙ t2) | _ | _ = nothing
  check Γ (A ↦ t) with check (Γ , A) t
  ... | just B = just (A ⇒ B)
  ... | _ = nothing


-----------------------------------------------------------------

module Semantics (TypeNames : Set)
                 (_≡d_ : (x y : TypeNames) → Dec (x ≡ y))
                 (val : TypeNames → Set) where

  open Syntax TypeNames _≡d_ public


  -- значение выражений для типов
  TValue : Type → Set
  TValue (* A) = val A 
  TValue (A ⇒ B) = TValue A → TValue B

  -- Env зависит от Γ и соответствует Γ.
  -- Env это модель!
  data Env : ∀ {n} → Context n → Set where
    ∅ : Env ∅
    _,_ : ∀ {n} {Γ : Context n} {A} → Env Γ → TValue A → Env (Γ , A)

  -- lookup for Env
  _[_] : ∀ {n} {Γ : Context n} → Env Γ → (i : Fin n) → TValue (lookup i Γ) 
  (_ , x) [ zero ] = x
  (E , _) [ suc i ] = E [ i ]

  
  -- Значение терма в окружении Env (при условии синтаксической выводимости t ⦂ A)
  Value : ∀ {n} {Γ : Context n} {A} → (t : Term n) → Env Γ → {p : Γ ⊢ t ⦂ A} → TValue A 
  Value (var i) E {⊢v} = E [ i ]
  Value (x ∙ y) E {⊢∙ p₁ p₂} = (Value x E {p₁}) (Value y E {p₂})
  Value (x ↦ y) E {⊢⇒ p} = λ z → Value y (E , z) {p}

  getType : ∀ {A} → TValue A → Type
  getType {A} _ = A
  
  -- выполнимость (суждений t ⦂ A) в модели.
  -- корректность выполняется явтоматически.
  data _⊩_⦂_ {n} {Γ : Context n} (m : Env Γ) (t : Term n) (A : Type) : Set where
    prf : ∀ p → m ⊩ t ⦂ getType (Value {A = A} t m {p = p})

  soundness : ∀ {n} {Γ : Context n} {t : Term n} {m : Env Γ} {A} → Γ ⊢ t ⦂ A → m ⊩ t ⦂ A
  soundness {n} {Γ} {t} {m} {A} p = prf p 

  completeness : ∀ {n} {Γ : Context n} {t : Term n} {m : Env Γ} {A} → m ⊩ t ⦂ A → Γ ⊢ t ⦂ A
  completeness (prf p) = p


  -- объединим значения для типов и термов
  
  data Expr (n : ℕ) : Set where
    ty : Type → Expr n
    tm : Term n → Expr n

  -- тип значений
  data V : Set₁ where
    Vty  : (A : Set) → V
    Vtmv : {A : Set} → (a : A) → V
    Vtm∙ : V → V → V
    Vtm⇒ : {A : Set} → (A → V) → V

  -- значения выражений в окружении
  _⟦_⟧ : ∀ {n} {Γ : Context n} → Env Γ → Expr n → V
  E ⟦ ty A ⟧         = Vty (TValue A)
  E ⟦ tm (var i) ⟧   = Vtmv (E [ i ])
  E ⟦ tm (t₁ ∙ t₂) ⟧ = Vtm∙ (E ⟦ tm t₁ ⟧) (E ⟦ tm t₂ ⟧) 
  E ⟦ tm (A ↦ t) ⟧   = Vtm⇒ λ z → _,_ {A = A} E z ⟦ tm t ⟧ 


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


_ : Term 4
_ = ((* nP) ↦ var (# 2)) ∙ var (# 3)

Γ : Context 3
Γ = ∅ , (* nP) , (* nQ) , (* nR)

E : Env Γ
E = ∅ , p , q , r 

_ : Value (var (# 0)) E {⊢v} ≡ r
_ = refl

_ : Value (var (# 2)) E {⊢v} ≡ p
_ = refl

_ : Value (* nP ↦ (var (# 0))) ∅ {⊢⇒ ⊢v} ≡ λ (x : P) → x 
_ = refl

_ : Value (* nP ↦ (var (# 2))) E {⊢⇒ ⊢v} ≡ λ (_ : P) → q
_ = refl

_ : Value (* nP ↦ * nR ↦ (var (# 3))) E {⊢⇒ (⊢⇒ ⊢v)} ≡ λ (x : P) (y : R) → q
_ = refl

_ : Value ((* nP ↦ (var (# 2))) ∙ (var (# 2))) E {⊢∙ (⊢⇒ ⊢v) ⊢v} ≡ q
_ = refl

_ : Value ((* nR ⇒ * nP) ↦ * nR ↦ (var (# 1)) ∙ (var (# 0))) ∅ {⊢⇒ (⊢⇒ (⊢∙ ⊢v ⊢v))}
        ≡ λ (x : (R → P)) (y : R) → x y
_ = refl

