{-# OPTIONS --prop #-}     -- enable Prop
-- TODO: пропозиции составляют решётку

module PropositionalLogic where

open import Agda.Builtin.Equality

id : {A : Prop} → A → A
id x = x


-- Интуиционистская пропозициональная логика
-- =========================================

module Intuitionistic where

  data ⊥ : Prop where

  data ⊤ : Prop where
    tt : ⊤

  data _∧_ (A B : Prop) : Prop where
    _,_ : A → B → A ∧ B

  fst : ∀ {A B} → A ∧ B → A
  fst (a , _) = a

  snd : ∀ {A B} → A ∧ B → B
  snd (_ , b) = b

  data _∨_ (A B : Prop) : Prop where
    inl : A → A ∨ B
    inr : B → A ∨ B

  ∨-elim : ∀ {A B C : Prop} → (f : A → C) → (g : B → C) → A ∨ B → C
  ∨-elim f g (inl x) = f x
  ∨-elim f g (inr x) = g x

  _⇒_ : Prop → Prop → Prop
  P ⇒ Q = P → Q

  _⇔_ : Prop → Prop → Prop
  P ⇔ Q = P ⇒ Q ∧ Q ⇒ P

  ¬ : Prop → Prop
  ¬ A = A ⇒ ⊥

  infixr 1 _⇒_ _⇔_
  
  ⊥-elim : ∀ {P : Prop} → ⊥ ⇒ P
  ⊥-elim = λ ()


  -- Несколько теорем

  _ : ∀ {P} → P ⇒ P
  _ = id

  ∧-comm : ∀ {P Q} → P ∧ Q ⇒ Q ∧ P
  ∧-comm (x , y) = (y , x)

  -- другой вид того же доказательства
  _ : ∀ {P Q} → P ∧ Q → Q ∧ P
  _ = λ p → (snd p , fst p)

  contradict : ∀ {P} → ¬ (P ∧ ¬ P)
  contradict (p , ¬p) = ¬p p

  contrapos : ∀ {P Q} → (P ⇒ Q) ⇒ ¬ Q ⇒ ¬ P
  contrapos p⇒q ¬q p = ¬q (p⇒q p)

  -- TODO: законы Моргана 

  deMorgan1 : ∀ {P Q} → ¬ (P ∨ Q) ⇔ ¬ P ∧ ¬ Q 
  deMorgan1 = {!!}

  -- В интуиционизме доказывается только в одну сторону
  deMorgan2⇒ : ∀ {P Q} → (¬ P) ∨ (¬ Q) ⇒ ¬ (P ∧ Q)
  deMorgan2⇒ = {!!}





-- Классическая пропозициональная логика
-- =====================================

-- Можно было бы просто добавить закон исключённого третьего (как делает
-- Agda), но мы сделаем иначе.

module Classic where

  open Intuitionistic renaming (_∧_ to _∧ⁱ_ ;
                                _∨_ to _∨ⁱ_ ;
                                _⇒_ to _⇒ⁱ_ ;
                                _⇔_ to _⇔ⁱ_ ;
                                ¬   to ¬ⁱ ;
                                ⊤   to ⊤ⁱ ;
                                ⊥   to ⊥ⁱ )

  -- Разрешимые пропозиции
  data Dec (A : Prop) : Set where
    yes : A → Dec A
    no  : ¬ⁱ A → Dec A

  -- Операции на разрешимых пропозициях
  _d∧_ : ∀ {P Q} → Dec P → Dec Q → Dec (P ∧ⁱ Q)
  (yes x) d∧ (yes y) = yes (x , y)
  _       d∧ (no  y) = no (λ z → y (snd z))
  (no x)  d∧ _       = no (λ z → x (fst z))

  _d∨_ : ∀ {P Q} → Dec P → Dec Q → Dec (P ∨ⁱ Q)
  (yes x) d∨ _       = yes (inl x)
  _       d∨ (yes y) = yes (inr y)
  (no x)  d∨ (no  y) = no (pp x y)
    where
    pp : ∀ {P Q} → ¬ⁱ P → ¬ⁱ Q → (P ∨ⁱ Q ) → ⊥ⁱ
    pp ¬p ¬q (inl x) = ¬p x
    pp ¬p ¬q (inr x) = ¬q x

  _d⇒_ : ∀ {P Q} → Dec P → Dec Q → Dec (P ⇒ⁱ Q)
  yes x d⇒ yes y = yes (λ x → y)
  yes x d⇒ no  y = no  (λ z → y (z x))
  no  x d⇒ yes y = yes (λ x → y)
  no  x d⇒ no  y = yes λ z → ⊥-elim (x z)

  d¬ : ∀ {P} → Dec P → Dec (¬ⁱ P)
  d¬ (yes x) = no (λ z → z x)
  d¬ (no  x) = yes x

  infixr 1 _d⇒_
  
  d⊤ : Dec ⊤ⁱ
  d⊤ = yes tt

  d⊥ : Dec ⊥ⁱ
  d⊥ = no id


  -- Тип разрешимых пропозиций
  data DecProp : (P : Prop) → Dec P → Set₁ where
    ax  : ∀ {P} → (p : Dec P) → DecProp P p    -- исходные пропозиции
    ⊤   : DecProp ⊤ⁱ d⊤    -- = ax d⊤
    ⊥   : DecProp ⊥ⁱ d⊥    -- = ax d⊥
    _∧_ : ∀ {P Q p q} → DecProp P p → DecProp Q q → DecProp (P ∧ⁱ Q) (p d∧ q)
    _∨_ : ∀ {P Q p q} → DecProp P p → DecProp Q q → DecProp (P ∨ⁱ Q) (p d∨ q)
    _⇒_ : ∀ {P Q p q} → DecProp P p → DecProp Q q → DecProp (P ⇒ⁱ Q) (p d⇒ q)
    ¬   : ∀ {P p} → DecProp P p → DecProp (¬ⁱ P) (d¬ p)

  infix 1 _⇒_
  
  -- Excluded Middle (для типа DecProp)
  LEM : ∀ {P p} → DecProp P p → Dec P
  LEM {P} {p} _ = p

  -- верно для разрешимых пропозиций
  deMorgan2⇐ : ∀ {P Q} (p : Dec P) (q : Dec Q) → Dec (¬ⁱ (P ∧ⁱ Q) ⇒ⁱ (¬ⁱ P) ∨ⁱ (¬ⁱ Q)) 
  deMorgan2⇐ (yes x) (yes y) = yes (λ z → inl (λ u → z (u , y))) 
  deMorgan2⇐ (yes x) (no  y) = yes (λ z → inr y) 
  deMorgan2⇐ (no  x) (yes y) = yes (λ z → inl x) 
  deMorgan2⇐ (no  x) (no  y) = yes (λ z → inl x)

  -- импликация
  impl⇒ : ∀ {P Q} (p : Dec P) (q : Dec Q) → Dec ((P ⇒ⁱ Q) ⇒ⁱ (¬ⁱ P) ∨ⁱ Q)
  impl⇒ (yes x) (yes y) = yes (λ z → inr (z x))
  impl⇒ (yes x) (no  y) = yes (λ z → inl (λ x → y (z x)))
  impl⇒ (no x) _ = yes (λ _ → inl x)

  impl⇐ : ∀ {P Q} (p : Dec P) (q : Dec Q) → Dec ((¬ⁱ P) ∨ⁱ Q ⇒ⁱ (P ⇒ⁱ Q))
  impl⇐ _       (yes y) = yes (λ _ _ → y)
  impl⇐ (yes x) (no  y) = yes λ u v → ∨-elim (λ z → ⊥-elim (z x)) id u
  impl⇐ (no  x) (no  y) = yes λ u v → ∨-elim (λ z → ⊥-elim (z v)) id u

  -- Объединение предыдущих двух утверждений
  impl : ∀ {P Q} (p : Dec P) (q : Dec Q) → Dec ((¬ⁱ P) ∨ⁱ Q ⇔ⁱ (P ⇒ⁱ Q))
  impl _ _ = yes (λ x _ → x) 



  -- перевод разрешимых типов в булевы значения

  data Bool : Set where
    true  : Bool
    false : Bool

  toBool : ∀ P {p} → {DecProp P p} → Bool
  toBool _ {yes _} = true
  toBool _ {no  _} = false

  getP : ∀ {P p} → DecProp P p → Prop
  getP {P} _ = P
  
  getp : ∀ {P p} → DecProp P p → Dec P
  getp {_} {p} _ = p
  
  



module Example where

  open import Data.Nat
  open Intuitionistic

  _is-even : ℕ → Prop 
  zero is-even = ⊤
  (suc (suc n)) is-even = n is-even
  _ is-even = ⊥
  
  -- Определить is-even как тип сложно, т.к. все его конструкторы должны совпадать.

