-- Простой язык. Agda используется как метаязык.

module _ where

open import Data.Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Совсем простой язык

module VerySimple where

  -- Выражения языка.
  data Expr : Set where
    var  : ℕ → Expr                     -- переменная
    plus : Expr → Expr → Expr           -- сложение выражений
  
  -- Значениями выражений являются числа.
  ⟦_⟧ : Expr → ℕ
  ⟦ var n ⟧ = n
  ⟦ plus n m ⟧ = ⟦ n ⟧ + ⟦ m ⟧


  _ : ⟦ plus (var 3) (var 5) ⟧ ≡ 8
  _ = refl



-- Усложним. Добавим имена для переменных

module m1 where

  module Syntax (VarNames : Set) where
  
    -- Выражения языка.
    data Expr : Set where
      var  : VarNames → Expr             -- имена для переменных
      plus : Expr → Expr → Expr

  module Semantics (VarNames : Set) (valuation : VarNames → ℕ) where

    open Syntax VarNames
    
    -- Значениями выражений являются числа.
    ⟦_⟧ : Expr → ℕ
    ⟦ var x ⟧ = valuation x
    ⟦ plus n m ⟧ = ⟦ n ⟧ + ⟦ m ⟧
  

  -- Пример

  data Names : Set where
    один два три четыре : Names

  val : Names → ℕ
  val один = 1
  val два = 2
  val три = 3
  val четыре = 4

  open Syntax Names
  open Semantics Names val

  _ : ⟦ plus (var один) (var три) ⟧ ≡ 4
  _ = refl

  -- Можно ввести обозначения для удобства.
  Один = var один
  Три  = var три

  _⨁_ = λ x y → plus x y
  
  _ : ⟦ Один ⨁ Три ⟧ ≡ 4
  _ = refl



-- Формализуем и значения языка тоже.

module m2 where

  -- Syntax остался прежним
  module Syntax (VarNames : Set) where
  
    -- Выражения языка.
    data Expr : Set where
      var  : VarNames → Expr
      plus : Expr → Expr → Expr

  -- Формализуем значения (смысл языка)
  data Value : Set where
    vz : Value                  -- zero
    vs : Value → Value          -- suc

  -- Смысл операции plus
  Vplus : Value → Value → Value
  Vplus vz y = y
  Vplus (vs x) y = vs (Vplus x y)


  module Semantics (VarNames : Set) (valuation : VarNames → Value) where

    open Syntax VarNames
    
    -- Значениями выражений являются Value.
    ⟦_⟧ : Expr → Value
    ⟦ var x ⟧ = valuation x
    ⟦ plus n m ⟧ = Vplus ⟦ n ⟧ ⟦ m ⟧


  -- Пример

  data Names : Set where
    один два три четыре : Names

  val : Names → Value
  val один   = vs vz
  val два    = vs (vs vz) 
  val три    = vs (vs (vs vz))
  val четыре = vs (vs (vs (vs vz)))

  open Syntax Names
  open Semantics Names val

  _ : ⟦ plus (var один) (var три) ⟧ ≡ vs (vs (vs (vs vz)))
  _ = refl




-- Добавим контекст
-- Используем индексы де Брёйна

module m3 where

  open import Data.Fin using (Fin; #_)

  module Syntax (VarNames : Set) where

    data Expr n : Set where
      var  : Fin n → Expr n
      plus : Expr n → Expr n → Expr n
      
    data Context : ℕ → Set where
      ∅   : Context 0
      _,_ : ∀ {n} → Context n → ℕ → Context (suc n)

    lookup : ∀ {n} → Fin n → Context n → ℕ
    lookup  Fin.zero   (xs , x) = x
    lookup (Fin.suc i) (xs , x) = lookup i xs 

    data _⊢_ {n} : Context n → Expr n → Set where
      ⊢v : ∀ {Γ} {i : Fin n}
         --------
         → Γ ⊢ (var i)

      ⊢+ : ∀ {Γ x y}
         → Γ ⊢ x
         → Γ ⊢ y
         -------
         → Γ ⊢ plus x y
  



-- Добавим типы.

module m4 where

  open import Data.Fin using (Fin; #_)

  module Syntax where

    data Type : Set where
      nat string : Type

    -- пре-термы, их корректность не проверяется
    data Term n : Set where
      var    : Fin n → Term n
      plus   : Term n → Term n → Term n           -- для чисел
      append : Term n → Term n → Term n           -- для строк

    -- Контекст состоит из типов
    data Context : ℕ → Set where
      ∅ : Context 0
      _,_ : ∀ {n} → Context n → Type → Context (suc n)

    infixl 4 _,_
    
    lookup : ∀ {n} → Fin n → Context n → Type
    lookup Fin.zero (_ , x) = x
    lookup (Fin.suc i) (xs , _) = lookup i xs

    infix 1 _⊢_⦂_
    
    -- выводятся только корректные термы, которые индексируются типами
    data _⊢_⦂_ {n} : Context n → Term n → Type → Set where
      ⊢v : ∀ {Γ i}
         -------
         → Γ ⊢ (var i) ⦂ lookup i Γ
      
      ⊢n : ∀ {Γ x y}
         → Γ ⊢ x ⦂ nat
         → Γ ⊢ y ⦂ nat
         -------------
         → Γ ⊢ plus x y ⦂ nat

      ⊢s : ∀ {Γ x y}
         → Γ ⊢ x ⦂ string
         → Γ ⊢ y ⦂ string
         -------------
         → Γ ⊢ append x y ⦂ string

    _ : ∅ , nat , nat ⊢ plus (var (# 0)) (var (# 1)) ⦂ nat
    _ = ⊢n ⊢v ⊢v

    _ : ∅ , string , nat , string ⊢ append (var (# 0)) (var (# 2)) ⦂ string
    _ = ⊢s ⊢v ⊢v


  module Semantics where

    open Syntax

    open import Data.String using (String; _++_)

    TValue : Type → Set
    TValue nat = ℕ
    TValue string = String

    data Env : ∀ {n} (Γ : Context n) → Set₁ where
      ∅   : Env ∅
      _,_ : ∀ {n} {Γ : Context n} {A : Type} → Env Γ → TValue A → Env (Γ , A)

    -- lookup for Env
    _[_] : ∀ {n} {Γ : Context n} → Env Γ → (i : Fin n) → TValue (lookup i Γ)  
    (_ , x) [ Fin.zero ] = x
    (E , _) [ Fin.suc i ] = E [ i ]
  
    
    -- Значение терма в окружении Env (при условии синтаксической выводимости t ⦂ A)
    Value : ∀ {n} {Γ : Context n} {A} → (t : Term n) → Env Γ → {p : Γ ⊢ t ⦂ A} → TValue A 
    Value (var i) E {⊢v} = E [ i ]
    Value (plus x y) E {⊢n p q} = (Value x E {p}) + (Value y E {q})
    Value (append x y) E {⊢s p q} = (Value x E {p}) ++ (Value y E {q})
  
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

