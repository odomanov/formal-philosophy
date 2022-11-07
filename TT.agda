-- Теория типов: Основные определения и свойства

module TT where

open import Agda.Primitive public  -- определяет универсумы Set ℓ и уровни.

-- одноэлементный тип
data ⊤ : Set where
  tt : ⊤

-- пустой тип -- абсурд, то, что не может иметь доказательства
data ⊥ : Set where

-- принцип индукции для ⊥
-- ex falso quodlibet
⊥-elim : ∀ {a} {Whatever : Set a} → ⊥ → Whatever
⊥-elim ()


-- отрицание
infix 3 ¬_
¬_ : ∀ {a} (A : Set a) → Set a
¬_ A = A → ⊥

-- Таким образом, доказательство отрицания это доказательство импликации.
-- В интуиционизме это называется сведением к абсурду.


-- доказательство из противоречия
contradiction : ∀ {a} {A P : Set a} → P → ¬ P → A
contradiction p ¬p = ⊥-elim (¬p p)

-- двойное отрицание
A⇒¬¬A : ∀ {a} {A : Set a} → A → ¬ ¬ A  -- → (A → ⊥) → ⊥
A⇒¬¬A x f = f x

-- В обратную сторону в интуиционизме не доказывается.
-- Если вы знаете, что тип непуст, то это не значит, что вы можете указать хотя бы
-- один элемент этого типа.

contrapositive : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → (¬ B → ¬ A)
contrapositive f v a = v (f a)

-- эквивалентность тройного отрицания и отрицания
¬¬¬⇒¬ : ∀ {a} {A : Set a} → ¬ ¬ ¬ A → ¬ A
¬¬¬⇒¬ = contrapositive A⇒¬¬A

¬⇒¬¬¬ : ∀ {a} {A : Set a} → ¬ A → ¬ ¬ ¬ A
¬⇒¬¬¬ = A⇒¬¬A                              -- A⇒¬¬A {¬ A}



-- Равенство
-- =========

infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

_≢_ : ∀ {a} {A : Set a} (x y : A) → Set a
x ≢ y = ¬ x ≡ y

-- полезная лемма
cong : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

-- подстановка
subst : ∀ {a b} {A : Set a} {x y : A} (P : A → Set b) → x ≡ y → P x → P y
subst P refl p = p 



-- Тип функций
-- ===========

-- Встроен в Агду, т.е. не требует определения.

-- Некоторые полезные функции ---------------------------------- 

-- Композиция функций
_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f(g(x))      -- = f (g x)

id : ∀ {A : Set} → A → A
id x = x

const : ∀ {A B : Set} → A → B → A
const c _ = c

_ : ∀ {A B} {c : A} → const c ≡ λ (_ : B) → c
_ = refl


-- использование скрытых аргументов
typeOf : ∀ {a} {A : Set a} → A → Set a
typeOf {_} {A} _ = A

typeOf' : ∀ {a} {A : Set a} → A → Set a
typeOf' {A = A} _ = A

-- два определения выше совпадают
_ : ∀ {a} {A : Set a} → (x : A) → typeOf x ≡ typeOf' x
_ = λ x → refl

levelOf : ∀ {a} {A : Set a} → A → Level
levelOf {a} _ = a

domain : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Set a
domain {A = A} _ = A

codomain : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Set b
codomain {B = B} _ = B


-- экстенсиональность функций в Агде не доказывается и обычно полагается
-- как дополнительная аксиома
Extensionality : (a b : Level) → Set _
Extensionality a b = {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
  (∀ x → f x ≡ g x) → f ≡ g
  



-- Тип истинностных значений
-- =========================

data Bool : Set where
  false true : Bool

-- Булевы операции
_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ b = false

_∨_ : Bool → Bool → Bool
true  ∨ b = true
false ∨ b = b

not : Bool → Bool
not true = false
not false = true

-- некоторые свойства ----------------------------------

∧-comm : ∀ x y → x ∧ y ≡ y ∧ x
∧-comm false false = refl
∧-comm false true = refl
∧-comm true false = refl
∧-comm true true = refl

∧-assoc : ∀ x y z → (x ∧ y) ∧ z ≡ x ∧ (y ∧ z)
∧-assoc true  y z = refl
∧-assoc false y z = refl

not-¬ : ∀ {x y} → x ≡ y → x ≢ not y   -- = x ≡ not y → ⊥
not-¬ {true}  refl ()
not-¬ {false} refl ()


-- Перевод из Bool в Set

T : Bool → Set
T true  = ⊤
T false = ⊥



-- Тип натуральных чисел
-- =====================

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

infix  4 _==_ _<_
infixl 6 _+_ _-_
infixl 7 _*_

_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)

-- Порядок в сложении может быть важен для доказательства:
0+m : ∀ m → zero + m ≡ m
0+m m = refl

m+0 : ∀ m → m + zero ≡ m
m+0 zero = refl
m+0 (suc m) = cong suc (m+0 m)

m+0' : ∀ m → m ≡ m + zero
m+0' zero = refl
m+0' (suc m) = cong suc (m+0' m)

m+0'' : ∀ m → m ≡ m + zero
m+0'' m = sym (m+0 m)
  where
  sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
  sym refl = refl

_-_ : ℕ → ℕ → ℕ
n     - zero = n
zero  - suc m = zero              -- в ℕ нет отрицательных чисел
suc n - suc m = n - m

_*_ : ℕ → ℕ → ℕ
zero  * m = zero
suc n * m = m + n * m

_==_ : ℕ → ℕ → Bool             -- булево равенство
zero  == zero  = true
suc n == suc m = n == m
_     == _     = false

_<_ : ℕ → ℕ → Bool
_     < zero  = false
zero  < suc _ = true
suc n < suc m = n < m


data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n}                 → zero  ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n

_≥_ : ℕ → ℕ → Set
m ≥ n = n ≤ m

_≰_ : ℕ → ℕ → Set
m ≰ n = ¬ m ≤ n

-- предыдущие два неравенства могут и не совпадать.
≰⇒≥ : ∀ m n → m ≰ n → m ≥ n
≰⇒≥ _ zero mn = z≤n
≰⇒≥ zero (suc n) mn = contradiction mn (λ z → z z≤n)
≰⇒≥ (suc m) (suc n) mn = s≤s (≰⇒≥ m n (λ z → mn (s≤s z)))

-- а в обратную сторону?
≥⇒≰ : ∀ m n → m ≥ n → m ≰ n
≥⇒≰ m n mn = {!!}

-- максимум двух чисел
Max : ℕ → ℕ → ℕ
Max zero    n       = n
Max (suc m) zero    = suc m
Max (suc m) (suc n) = suc (Max m n)


-- докажем несколько утверждений
0≢1+n : ∀ {n} → zero ≢ suc n
0≢1+n ()

1+n≢0 : ∀ {n} → suc n ≢ zero
1+n≢0 ()

n≤0⇒n≡0 : ∀ {n} → n ≤ zero → n ≡ zero
n≤0⇒n≡0 z≤n = refl



-- Списки
-- ====== 

infixr 5 _∷_
data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

-- принцип индукции
List-ind : ∀ {a c} {A : Set a} (C : List A → Set c)
           → C []
           → ((x : A) (xs : List A) → C (x ∷ xs))
           --------------------------------------
           → ((x : List A) → C x)
List-ind C p0 p [] = p0
List-ind C p0 p (x ∷ xs) = p x xs


-- некоторые полезные функции для списков --------------------------------

-- конкатенация списков
infixr 5 _++_
_++_ : ∀ {a} {A : Set a} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

-- свёртка справа
foldr : ∀ {a b} {A : Set a} {B : Set b}
        → (A → B → B) → B → List A → B
foldr f b0 []       = b0
foldr f b0 (x ∷ xs) = f x (foldr f b0 xs)

-- свёртка слева
foldl : ∀ {a b} {A : Set a} {B : Set b}
        → (B → A → B) → B → List A → B
foldl f b0 []       = b0
foldl f b0 (x ∷ xs) = foldl f (f b0 x) xs


sum : List ℕ → ℕ
sum = foldr _+_ zero

and : List Bool → Bool
and = foldr _∧_ true

length : ∀ {a} {A : Set a} → List A → ℕ
length = foldr (λ _ y → suc y) zero

-- Теорема: длина конкатенации равна сумме длин 
length-++ : ∀ {a} {A : Set a} → (xs : List A) → (ys : List A) 
            → length (xs ++ ys) ≡ length xs + length ys
length-++ []       _ = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)


-- Тип Maybe
-- =========

data Maybe {a} (A : Set a) : Set a where
  just    : A → Maybe A
  nothing : Maybe A

-- применения типа Maybe --------------------------------------- 

-- первый элемент списка
head : ∀ {a} {A : Set a} → List A → Maybe A
head []      = nothing                         -- у пустого списка нет первого элемента
head (x ∷ _) = just x

-- хвост списка
tail : ∀ {a} {A : Set a} → List A → Maybe (List A)
tail []       = nothing
tail (_ ∷ xs) = just xs

-- последний элемент списка
last : ∀ {a} {A : Set a} → List A → Maybe A
last []       = nothing
last (x ∷ []) = just x
last (_ ∷ xs) = last xs


is-just : ∀ {a} {A : Set a} → Maybe A → Bool
is-just (just _) = true
is-just nothing  = false


-- Σ-тип или тип пар
-- =================

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where  -- ⊔ это функция максимума
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public   -- сделать proj₁, proj₂ доступными

infixr 4 _,_


-- Принцип индукции для Σ-типа:
Σ-induction : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Σ A B → Set c}
              → (∀ x y → C (x , y))
              -----------------
              → ((p : Σ A B) → C p)
Σ-induction f (x , y) = f x y

-- Определим удобный синтаксис
-- (в Агде определено немного не так, но принцип тот же)

syntax Σ A (λ x → B) = Σ[ x ∈ A ] B


-- Отдельное обозначение для независимых типов (декартово произведение)
infixr 2 _×_
_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ A (λ _ → B)                                 -- = Σ[ x ∈ A ] B

-- функции каррирования
curry : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Σ A B → Set c} 
        → ((p : Σ A B) → C p) 
        → ((x : A) → (y : B x) → C (x , y))
curry f x y = f (x , y)

-- ср. с Σ-induction
uncurry : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Σ A B → Set c} →
          ((x : A) → (y : B x) → C (x , y)) →
          ((p : Σ A B) → C p)
uncurry f (x , y) = f x y

-- curry и uncurry показывают эквивалентность A × B → C и A → (B → C).
-- Или, в общем случае, Σ A B → C и (x : A) → (B x → C).



-- Тип дизъюнктивной суммы
-- =======================

infixr 1 _⊎_

data _⊎_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

-- принцип индукции
[_,_] : ∀ {a b c} {A : Set a} {B : Set b} {C : A ⊎ B → Set c}
        → ((x : A) → C (inj₁ x))
        → ((x : B) → C (inj₂ x)) 
        → ((x : A ⊎ B) → C x)
[ f , g ] (inj₁ x) = f x
[ f , g ] (inj₂ y) = g y



-- Вектор -- тип списков длины n
-- =============================

data Vec {a} (A : Set a) : ℕ → Set a where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

-- Функции head-v и tail-v не требуют Maybe, в отличие от List.
-- Они не определены для пустого вектора.
head-v : ∀ {a} {A : Set a} {n} → Vec A (suc n) → A
head-v (x ∷ xs) = x

tail-v : ∀ {a} {A : Set a} {n} → Vec A (suc n) → Vec A n
tail-v (x ∷ xs) = xs

-- конкатенация векторов похожа на конкатенацию списков
_+++_ : ∀ {a} {A : Set a} {m n} → Vec A m → Vec A n → Vec A (m + n)
[]       +++ ys = ys
(x ∷ xs) +++ ys = x ∷ (xs +++ ys)


