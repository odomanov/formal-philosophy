-- Агда как метаязык

-- Моделирование пропозициональной логики
-- ======================================

module PropositionalLogic-Meta where

open import TTCore hiding (_++_)


--==  Синтаксис  ==--

module Syntax (Atom : Set) where

  infixl 4 _,_
  infix 5 _++_
  -- infix 6 _∋_
  infix 7 _⊢_
  infix 8 ⟪_⟫ _∧_ _∨_ _⇒_  

  data Proposition : Set where
    ⟪_⟫ : Atom → Proposition
    F   : Proposition
    T   : Proposition
    _⇒_ : Proposition → Proposition → Proposition
    _⇔_ : Proposition → Proposition → Proposition
    _∧_ : Proposition → Proposition → Proposition
    _∨_ : Proposition → Proposition → Proposition
    ~   : Proposition → Proposition
  
  data Context : Set where
    ∅   : Context
    _,_ : Context → Proposition → Context
  
  _++_ : Context → Context → Context
  xs ++ ∅ = xs
  xs ++ (ys , y) = (xs ++ ys) , y
  
  
  -- правила вывода (natural deduction), синтаксический вывод
  data _⊢_ : Context → Proposition → Set where
    ~i : ∀ {Γ P Q}
       → Γ ⊢ P ⇒ Q
       → Γ ⊢ P ⇒ ~ Q
         ------------
       → Γ ⊢ ~ P
  
    ~e : ∀ {Γ P Q}
       → Γ ⊢ ~ P
         ---------
       → Γ ⊢ P ⇒ Q
  
    ~~e : ∀ {Γ P}
        → Γ ⊢ ~ (~ P)
          --------- 
        → Γ ⊢ P
  
    ∧i : ∀ {Γ P Q}
       → Γ ⊢ P
       → Γ ⊢ Q
         -----
       → Γ ⊢ P ∧ Q
  
    ∧el : ∀ {Γ P Q}
       → Γ ⊢ P ∧ Q
         -----
       → Γ ⊢ P
  
    ∧er : ∀ {Γ P Q}
       → Γ ⊢ P ∧ Q
         -----
       → Γ ⊢ Q
  
    ∨il : ∀ {Γ P Q}
       → Γ ⊢ P
         -----
       → Γ ⊢ P ∨ Q
  
    ∨ir : ∀ {Γ P Q}
       → Γ ⊢ Q
         -----
       → Γ ⊢ P ∨ Q
  
    ⇔i : ∀ {Γ P Q}
       → Γ ⊢ P ⇒ Q
       → Γ ⊢ Q ⇒ P
         -----
       → Γ ⊢ P ⇔ Q
  
    ⇔el : ∀ {Γ P Q}
       → Γ ⊢ P ⇔ Q 
         -----
       → Γ ⊢ P ⇒ Q
  
    ⇔er : ∀ {Γ P Q}   -- нужно ли два правила для ⇔e ?
       → Γ ⊢ P ⇔ Q 
         -----
       → Γ ⊢ Q ⇒ P
  
    ⇒i : ∀ {Γ P Q}
       → (Γ , P) ⊢ Q
         -----
       → Γ ⊢ P ⇒ Q
  
    ⇒e : ∀ {Γ P Q}   -- modus ponens
       → Γ ⊢ P
       → Γ ⊢ P ⇒ Q
         -----
       → Γ ⊢ Q



--==  Semantics  ==--

module Semantics (Atom : Set) where

  open Syntax Atom public
  
  -- Операции на Bool
  _AND_ : Bool → Bool → Bool
  true AND true = true
  _ AND _ = false
  
  _OR_ : Bool → Bool → Bool
  false OR false = false
  _ OR _ = true
  
  NOT : Bool → Bool
  NOT true  = false
  NOT false = true
  
  _=>_ : Bool → Bool → Bool
  P => Q = (NOT P) OR Q 
  
  _<=>_ : Bool → Bool → Bool
  P <=> Q = (P => Q) AND (Q => P)
  
  infix 2 _AND_ _OR_
  
  record Model : Set₁ where
    field
      val : Atom → Bool 
  
  open Model
  
  -- Значение в модели
  _⟦_⟧ : Model → Proposition → Bool
  m ⟦ ⟪ x ⟫ ⟧ = (val m) x
  m ⟦ F ⟧ = false
  m ⟦ T ⟧ = true
  m ⟦ P ∧ Q ⟧ = m ⟦ P ⟧ AND m ⟦ Q ⟧
  m ⟦ P ∨ Q ⟧ = m ⟦ P ⟧ OR m ⟦ Q ⟧
  m ⟦ ~ P ⟧   = NOT (m ⟦ P ⟧)
  m ⟦ P ⇒ Q ⟧ = NOT (m ⟦ P ⟧) OR m ⟦ Q ⟧
  m ⟦ P ⇔ Q ⟧ = (m ⟦ P ⟧ AND m ⟦ Q ⟧) OR (NOT (m ⟦ P ⟧) AND NOT (m ⟦ Q ⟧))
  
  
  -- Все пропозиции в контексте удовлетворяют Pred
  All : Context → (Pred : Proposition → Set) → Set
  All ∅ P = ⊤
  All (Γ , x) P = All Γ P × P x
  
  
  -- Выполнимость в любой модели (семантический вывод)
  _⊩_ : Context → Proposition → Set₁
  Γ ⊩ P = ∀ (m : Model) → All Γ (λ x → m ⟦ x ⟧ ≡ true) → m ⟦ P ⟧ ≡ true
  
  
  -- Формулировки теорем. Докажем только корректность, доказательство
  -- полноты см.: Leran Cai, Ambrus Kaposi, and Thorsten Altenkirch
  -- "Formalising the Completeness Theorem of Classical Propositional Logic
  -- in Agda (Proof Pearl)"
  -- http://bitbucket.org/Leran/propositional-logic


  -- Полнота:
  -- =======
  completeness : ∀ {Γ P} → Γ ⊩ P → Γ ⊢ P
  completeness = {!!}



  -- Корректность:
  -- ============

  soundness : ∀ {Γ P} → Γ ⊢ P → Γ ⊩ P
  soundness (~i p q) m γ = lemma _ _ (soundness p m γ) (soundness q m γ)
    where
    lemma : ∀ x y → x => y ≡ true → x => NOT y ≡ true → NOT x ≡ true
    lemma true true refl = λ ()
    lemma true false () 
    lemma false true refl q = refl
    lemma false false p q = refl
  soundness (~e p)   m γ = lemma _ _ (soundness p m γ)
    where
    lemma : ∀ x y → (NOT x) ≡ true → ((NOT x) OR y) ≡ true
    lemma false true refl = refl
    lemma false false refl = refl
  soundness (~~e p) m γ = lemma _ (soundness p m γ)
    where
    lemma : ∀ x → NOT (NOT x) ≡ true → x ≡ true
    lemma true refl = refl
  soundness (∧i p q) m γ = lemma _ _ (soundness p m γ) (soundness q m γ)
    where
    lemma : ∀ x y → x ≡ true → y ≡ true → (x AND y) ≡ true
    lemma .true .true refl refl = refl
  soundness (∧el p)  m γ = lemma _ _ (soundness p m γ)
    where
    lemma : ∀ x y → (x AND y) ≡ true → x ≡ true
    lemma true true refl = refl
  soundness (∧er p)  m γ = lemma _ _ (soundness p m γ)
    where
    lemma : ∀ x y → (x AND y) ≡ true → y ≡ true
    lemma true true refl = refl
  soundness (∨il p)  m γ = lemma _ _ (soundness p m γ)
    where
    lemma : ∀ x y → x ≡ true → (x OR y) ≡ true
    lemma true _ refl = refl
  soundness (∨ir p)  m γ = lemma _ _ (soundness p m γ)
    where
    lemma : ∀ x y → y ≡ true → (x OR y) ≡ true
    lemma true true refl = refl
    lemma false true refl = refl
  soundness {Γ} {P ⇒ Q} (⇒i p)   m γ with m ⟦ P ⟧ | inspect (λ x → m ⟦ x ⟧) P
  ... | true | [ eq ] = lemma _ _ (soundness p m (γ , eq))
    where
    lemma : ∀ x y → y ≡ true → ((NOT x) OR y) ≡ true
    lemma true true refl = refl
    lemma false true refl = refl
  ... | false | _ = refl
  soundness (⇒e p q) m γ = lemma _ _ (soundness p m γ) (soundness q m γ)
    where
    lemma : ∀ x y → x ≡ true → (x => y) ≡ true → y ≡ true
    lemma true true refl refl = refl
  soundness (⇔i p q) m γ = lemma _ _ (soundness p m γ) (soundness q m γ)
    where
    lemma : ∀ x y → ((NOT x) OR y) ≡ true → ((NOT y) OR x) ≡ true
                  → ((x AND y) OR ((NOT x) AND (NOT y))) ≡ true
    lemma true true _ _ = refl
    lemma false false _ _ = refl
  soundness (⇔el p)  m γ = lemma _ _ (soundness p m γ)
    where
    lemma : ∀ x y → ((x AND y) OR ((NOT x) AND (NOT y))) ≡ true → ((NOT x) OR y) ≡ true
    lemma true true refl = refl
    lemma false false refl = refl
  soundness (⇔er p)  m γ = lemma _ _ (soundness p m γ)
    where
    lemma : ∀ x y → ((x AND y) OR ((NOT x) AND (NOT y))) ≡ true → ((NOT y) OR x) ≡ true
    lemma true true refl = refl
    lemma false false refl = refl
  



-- Пример

data Atom : Set where AP AQ AR : Atom

open Semantics Atom

M : Model
M = record { val = v }
  where
  v : Atom → Bool
  v AP = true
  v AQ = false
  v AR = true

P = ⟪ AP ⟫
Q = ⟪ AQ ⟫
R = ⟪ AR ⟫

_ : M ⟦ P ∧ Q ⟧ ≡ false
_ = refl

_ : M ⟦ P ∧ (~ Q ∨ R) ⟧ ≡ true
_ = refl
  
