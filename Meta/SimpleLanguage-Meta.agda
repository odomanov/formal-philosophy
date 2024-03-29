-- Простой язык. Agda используется как метаязык.
-- Иллюстрация различных подходов к формализации языков.

module _ where

open import Data.Nat using (ℕ; zero; suc; _+_; _<?_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; inspect)


-- =========================================================================
-- Совсем простой язык

module VerySimple where

  -- Выражения языка.
  data Expr : Set where
    cnst : ℕ → Expr                     -- константа (число)
    plus : Expr → Expr → Expr           -- сложение выражений
  
  -- Значениями выражений являются числа.
  ⟦_⟧ : Expr → ℕ
  ⟦ cnst n ⟧ = n
  ⟦ plus n m ⟧ = ⟦ n ⟧ + ⟦ m ⟧


  _ : ⟦ plus (cnst 3) (cnst 5) ⟧ ≡ 8
  _ = refl



-- =========================================================================
-- Усложним. Добавим переменные с именами.
-- И выделим модули для синтаксиса и семантики.

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

  _ : ⟦ plus (var один) (plus (var три) (var два)) ⟧ ≡ 6
  _ = refl


  -- Можно ввести обозначения для удобства.
  Один = var один
  Два  = var два
  Три  = var три

  _∔_ = λ x y → plus x y
  
  _ : ⟦ Один ∔ Три ⟧ ≡ 4
  _ = refl

  _ : ⟦ Один ∔ (Три ∔ Два) ⟧ ≡ 6
  _ = refl




-- =========================================================================
-- Введём понятие модели 

module m2 where

  module Syntax (VarNames : Set) where
  
    -- Выражения языка.
    data Expr : Set where
      var  : VarNames → Expr             -- имена для переменных
      plus : Expr → Expr → Expr

  record Model (VarNames : Set) : Set where
    field
      valuation : VarNames → ℕ
    
  module Semantics (VarNames : Set) (m : Model VarNames) where

    open Syntax VarNames
    
    -- Значениями выражений являются числа.
    _⟦_⟧ : Model VarNames → Expr → ℕ
    m ⟦ var x ⟧ = Model.valuation m x
    m ⟦ plus i j ⟧ = m ⟦ i ⟧ + m ⟦ j ⟧
  

  -- Пример

  data Names : Set where
    один два три четыре : Names

  M : Model Names
  M = record { valuation = val}
    where
    val : Names → ℕ
    val один = 1
    val два = 2
    val три = 3
    val четыре = 4

  open Syntax Names
  open Semantics Names M

  _ : M ⟦ plus (var один) (var три) ⟧ ≡ 4
  _ = refl

  -- Можно ввести обозначения для удобства.
  Один = var один
  Три  = var три

  _∔_ = λ x y → plus x y
  
  _ : M ⟦ Один ∔ Три ⟧ ≡ 4
  _ = refl





-- =========================================================================
-- Формализуем и значения языка тоже.

module m3 where

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


  record Model (VarNames : Set) : Set where
    field
      valuation : VarNames → Value
    
  module Semantics (VarNames : Set) (m : Model VarNames) where

    open Syntax VarNames
    open Model m                 -- чтобы не писать Model.valuation m
    
    -- Значениями выражений являются Value.
    _⟦_⟧ : Model VarNames → Expr → Value
    m ⟦ var x ⟧ = valuation x
    m ⟦ plus i j ⟧ = Vplus (m ⟦ i ⟧) (m ⟦ j ⟧)


  -- Пример

  data Names : Set where
    один два три четыре : Names

  M : Model Names
  M = record { valuation = val }
    where
    val : Names → Value
    val один   = vs vz
    val два    = vs (vs vz) 
    val три    = vs (vs (vs vz))
    val четыре = vs (vs (vs (vs vz)))

  open Syntax Names
  open Semantics Names M

  _ : M ⟦ plus (var один) (var три) ⟧ ≡ vs (vs (vs (vs vz)))
  _ = refl





-- =========================================================================
-- Добавим контекст и типы.
-- Используем индексы де Брёйна (de Bruijn).
-- Контекст это список переменных, окружение (Env) это значения этих
-- переменных (валюация).  Т.е. Env это модель.
-- Имена переменных не нужны, достаточно номеров в списке.

module m4 where

  open import Data.Fin using (Fin; #_)

  module Syntax where

    data Type : Set where
      nat string : Type

    -- пред-термы, их корректность не гарантируется
    data Term n : Set where
      var    : Fin n  → Term n
      plus   : Term n → Term n → Term n           -- для чисел
      append : Term n → Term n → Term n           -- для строк

    -- Контекст содержит информацию о переменных. В данном случае он
    -- состоит из типов переменных.
    data Context : ℕ → Set where
      ∅ : Context 0
      _,_ : ∀ {n} → Context n → Type → Context (suc n)

    infixl 4 _,_
    
    lookup : ∀ {n} → Fin n → Context n → Type
    lookup Fin.zero (_ , x) = x
    lookup (Fin.suc i) (xs , _) = lookup i xs

    infix 1 _⊢_⦂_
    
    -- Выводятся только корректные термы, которые индексируются типами.
    -- Т.е. это правила построения термов.
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

    -- Примеры
    
    _ : ∅ , nat , nat ⊢ plus (var (# 0)) (var (# 1)) ⦂ nat
    _ = ⊢n ⊢v ⊢v

    _ : ∅ , string , nat , string ⊢ append (var (# 0)) (var (# 2)) ⦂ string
    _ = ⊢s ⊢v ⊢v

    -- а это не имеет доказательства
    _ : ∅ , string , nat , string ⊢ append (var (# 0)) (var (# 1)) ⦂ string
    _ = ⊢s ⊢v {!!}


  module Semantics where

    open import Data.String using (String; _++_)
    open import Function using (typeOf)
    
    open Syntax

    -- Значения для типов (берутся из Агды)
    TValue : Type → Set
    TValue nat = ℕ
    TValue string = String

    -- Env содержит значения (интерпретации) для переменных контекста.
    -- Env автоматически соответствует контексту.
    data Env : ∀ {n} (Γ : Context n) → Set₁ where
      ∅   : Env ∅
      _,_ : ∀ {n} {Γ : Context n} {A : Type} → Env Γ → TValue A → Env (Γ , A)

    -- lookup for Env
    _[_] : ∀ {n} {Γ : Context n} → Env Γ → (i : Fin n) → TValue (lookup i Γ)  
    (_ , x) [ Fin.zero ] = x
    (E , _) [ Fin.suc i ] = E [ i ]
  
    
    -- Значение терма в окружении Env (при условии синтаксической выводимости t ⦂ A)
    Value : ∀ {n} {Γ : Context n} {A} → Env Γ → (t : Term n) → (p : Γ ⊢ t ⦂ A) → TValue A 
    Value E (var i)       ⊢v      = E [ i ]
    Value E (plus x y)   (⊢n p q) = (Value E x p) +  (Value E y q)
    Value E (append x y) (⊢s p q) = (Value E x p) ++ (Value E y q)
  

    -- См. определение ⊩ ниже.
    _ : ∀ {n} {Γ : Context n} {A} {E : Env Γ}{t : Term n} {p} → typeOf (Value E t p) ≡ TValue A
    _ = refl

    -- Выполнимость (суждений t ⦂ A) в модели.
    -- ⊩prf означает, что если я посчитаю значение t в модели, то его тип (в модели)
    --   будет равен значению A.
    data _⊩_⦂_ {n} {Γ : Context n} (m : Env Γ) (t : Term n) (A : Type) : Set₁ where
      ⊩prf : ∀ p → typeOf (Value {A = A} m t p) ≡ TValue A → m ⊩ t ⦂ A 

    -- В этом определении "typeOf (Value {A = A} m t p) ≡ TValue A" можно было бы
    -- опустить, поскольку это равенство выполнено, если есть p.  Но я его оставил
    -- для наглядности.
    -- Т.е. можно было бы написать "⊩prf : (Γ ⊢ t ⦂ A) → m ⊩ t ⦂ A".
    -- Тогда это совпало бы с формулировкой для soundness ниже.


    soundness : ∀ {n} {Γ : Context n} {t : Term n} {m : Env Γ} {A}
                → Γ ⊢ t ⦂ A → m ⊩ t ⦂ A
    soundness p = ⊩prf p refl 
  
    completeness : ∀ {n} {Γ : Context n} {t : Term n} {m : Env Γ} {A}
                   → m ⊩ t ⦂ A → Γ ⊢ t ⦂ A
    completeness (⊩prf p r) = p






-- =========================================================================
-- Другое представление языка.  Правила вывода содержатся в термах. Поэтому
-- термы всегда корректны.

module m5 where

  open import Data.Fin using (Fin; #_)

  module Syntax where

    open import Data.Empty
    open import Data.Maybe
    open import Data.Product
    open import Data.Unit 
    open import Relation.Nullary using (Dec; yes; no)
    open import Relation.Nullary.Decidable.Core using (fromWitness)

    data Type : Set where
      nat string : Type

    -- Контекст содержит информацию о переменных. В данном случае он
    -- состоит из типов переменных.
    data Context : ℕ → Set where
      ∅ : Context 0
      _,_ : ∀ {n} → Context n → Type → Context (suc n)

    infixl 4 _,_
    
    lookup : ∀ {n} → Fin n → Context n → Type
    lookup Fin.zero (_ , x) = x
    lookup (Fin.suc i) (xs , _) = lookup i xs

    -- Эти термы всегда корректны.
    -- Терм Term Γ A имеет тип A в контексте Γ.
    -- В некоторых книгах представляют Term Γ A как Γ ⊢ A. 
    data Term {n} (Γ : Context n) : Type → Set where
      var    : (i : Fin n) → Term Γ (lookup i Γ)
      plus   : Term Γ nat    → Term Γ nat    → Term Γ nat       -- для чисел
      append : Term Γ string → Term Γ string → Term Γ string    -- для строк


    -- Синтаксическая выводимость суждения t : A
    data _⊢_⦂_ {n} (Γ : Context n) : ∀ {A} → Term Γ A → Type → Set where
      prf : ∀ {A} {t : Term Γ A} → Γ ⊢ t ⦂ A



    ----------------------------------------------------------------------------------
    -- Другой способ проверки термов (мы не будем его использовать)
    
    module m where
    
      -- Выражение выглядит как терм, но может не быть корректным.
      data Expr : Set where
        var    : ℕ → Expr
        plus   : Expr → Expr → Expr
        append : Expr → Expr → Expr
      
      -- Проверка корректности Expr в контексте Γ.
      check : ∀ {n} (Γ : Context n) (e : Expr) → Maybe (Σ Type (Term Γ))
      check {n} Γ (var i) with i <? n 
      ... | yes p = just ((lookup (#_ i {m<n = fromWitness p}) Γ) , var (# i))
      ... | no  _ = nothing
      check Γ (plus e₁ e₂) with check Γ e₁ | check Γ e₂
      ... | just (nat , -e₁) | just (nat , -e₂) = just (nat , plus -e₁ -e₂)
      ... | _                | _                = nothing
      check Γ (append e₁ e₂) with check Γ e₁ | check Γ e₂
      ... | just (string , -e₁) | just (string , -e₂) = just (string , append -e₁ -e₂)
      ... | _                   | _                   = nothing
      
    ----------------------------------------------------------------------------------
    


  -- Вернёмся к семантике
  
  module Semantics where
  
    open import Data.Unit 
    open import Function using (typeOf)

    open Syntax 

    open import Data.String using (String; _++_)
  
    -- значение выражений для типов
    TValue : Type → Set
    TValue nat = ℕ
    TValue string = String
  
    data Env : ∀ {n} → Context n → Set where
      ∅ : Env ∅
      _,_ : ∀ {n} {Γ : Context n} {A} → Env Γ → TValue A → Env (Γ , A)
  
    -- lookup for Env
    _[_] : ∀ {n} {Γ : Context n} → Env Γ → (i : Fin n) → TValue (lookup i Γ) 
    (_ , x) [ Fin.zero ] = x
    (E , _) [ Fin.suc i ] = E [ i ]
  
    
    -- Значение терма в окружении Env 
    Value : ∀ {n} {Γ : Context n} {A} → Env Γ → Term Γ A → TValue A
    Value E (var i)        = E [ i ]
    Value E (plus t₁ t₂)   = (Value E t₁) +  (Value E t₂)
    Value E (append t₁ t₂) = (Value E t₁) ++ (Value E t₂)


    -- См. определение ⊩ ниже.
    _ : ∀ {n} {Γ : Context n} {A} {E : Env Γ} {t : Term Γ A} → typeOf (Value E t) ≡ TValue A
    _ = refl

    -- выполнимость (суждений t ⦂ A) в модели.
    -- ⊩prf означает, что если я посчитаю значение t в модели, то его тип (в модели)
    --   будет равен значению A.
    data _⊩_⦂_ {n} {Γ : Context n} {A} (m : Env Γ) (t : Term Γ A) : Type → Set₁ where
      ⊩prf : typeOf (Value m t) ≡ TValue A → m ⊩ t ⦂ A  

    -- Здесь также "typeOf (Value m t) ≡ TValue A" можно было бы опустить.


    -- корректность и полнота тривиальны
    soundness : ∀ {n} {Γ : Context n} {A} {t : Term Γ A} {m : Env Γ} → Γ ⊢ t ⦂ A → m ⊩ t ⦂ A
    soundness prf = ⊩prf refl

    completeness : ∀ {n} {Γ : Context n} {A} {t : Term Γ A} {m : Env Γ} → m ⊩ t ⦂ A → Γ ⊢ t ⦂ A
    completeness (⊩prf refl) = prf

