-- Agda. Краткая инструкция
-- Документация: \url{https://agda.readthedocs.io/en/v2.6.0/} (не последняя версия!).

-- Каждый файл должен содержать главный модуль, имя которого совпадает с именем файла.

module L1 where

-- Основной разделитель --- пробел.  
-- Отступы отмечают блоки.

-- Set: универсум типов.



-- Определения типов --
-- ================= --

-- Тип истинностных значений:
data Bool : Set where
  true  : Bool
  false : Bool


-- Тип натуральных чисел:    
data Nat : Set where
  zero : Nat
  suc  : Nat → Nat    


-- Как видно, конструкторы имеют тип в качестве области значения.


-- пустой тип
data ⊥ : Set where

-- всегда истинный тип
data ⊤ : Set where
  tt : ⊤



-- Функции --
-- ======= --

-- (x : A) → B  или A → B
-- (x y : A) → B или A → A → B
-- (x : A) → (y : B) → C или A → B → C


-- Примеры

-- f = x + 2
f : Nat → Nat
f zero = suc (suc zero)           -- f(0) = 2
f (suc n) = suc (suc (suc n))     -- f(n) = n + 2

f' : Nat → Nat
f' n = suc (suc n)

a = f zero

_g : Nat → Nat
_g n = suc (suc n)
-- можно было бы:
-- n g = suc (suc n)


b1 = zero g
b2 = _g zero 

_+2 : Nat → Nat
_+2 n = suc (suc n)

b3 = zero +2

b4 = (suc (suc zero)) +2


module plus where

  _+_ : Nat → Nat → Nat
  zero  + zero  = zero
  zero  + suc n = suc n
  suc n + zero  = suc n 
  suc n + suc m = suc (n + suc m)


_+_ : Nat → Nat → Nat
zero  + n = n
suc n + m = suc (n + m)


c = b1 + a


предыдущее : Nat → Nat
предыдущее zero = zero
предыдущее (suc n) = n


f1 = λ (n : Nat) → suc (suc n) 
f2 = \ (n : Nat) → suc (suc n) 
f3 = \ (n : Nat) → n +2
f4 = λ (n : Nat) → n + (suc (suc zero))



-- Пример функции в зависимый тип

module m3 where

  data Страна : Set where
    Япония Буркина-Фасо : Страна

  -- индексированный тип
  data Город : Страна → Set where
    Токио        : Город Япония
    Саппоро      : Город Япония
    Уагадугу     : Город Буркина-Фасо
    Бобо-Диуласо : Город Буркина-Фасо
  
  столица : (x : Страна) → Город x
  столица Япония = Токио
  столица Буркина-Фасо = Уагадугу
  
  столица' : ∀ (x : Страна) → Город x
  столица' = столица
  
  столица'' : ∀ (x : _) → Город x
  столица'' = столица
  
  столица''' : ∀ x → Город x
  столица''' = столица 

  столица'''' : ∀ (x y : Страна) → Город x
  столица'''' x y = столица x



-- Функции могут иметь скрытые аргументы:

module m4 where

  data Страна : Set where
    Япония Буркина-Фасо : Страна
  
  data Город : {Страна} → Set where
    Токио        : Город {Япония}
    Саппоро      : Город {Япония}
    Уагадугу     : Город {Буркина-Фасо}
    Бобо-Диуласо : Город {Буркина-Фасо}
  
  столица : (x : Страна) → Город {x} 
  столица Япония = Токио
  столица Буркина-Фасо = Уагадугу
  
  столица' : ∀ (x : Страна) → Город 
  столица' = столица
  
  столица'' : ∀ x → Город 
  столица'' = столица 


-- Примеры скрытых аргументов

id : (A : Set) → A → A
id A x = x

id' : (A : Set) → A → A
id' _ x = x

id'' : {A : Set} → A → A
id'' x = x


type-of : {A : Set} (x : A) → Set
type-of {A} x = A


-- Проверить нормализацию type-of (С-c C-n)



-- Предикаты можно задавать индексированными типами.

data Even : Nat → Set where
  even-zero  : Even zero
  even-plus2 : {n : Nat} → Even n → Even (suc (suc n))

-- Здесь Even n это пропозиция "n чётно".
-- Мы задаём конструктор для всех n : Nat.



module m3' where
  open m3

  data естьСтолица : {x : Страна} → Город x → Set where
    есть-столица : ∀ {x} → естьСтолица (столица x)
    
  data Столица : Set where
    ст : ∀ {x} → (г : Город x) → естьСтолица г → Столица

  _ : Столица
  _ = ст Токио есть-столица

  _ : Столица
  _ = ст Уагадугу есть-столица




-- Пример. Возможные миры.
-- =======================

data World : Set where
  w1 w2 w3 : World

data Object : Set where
  o1 o2 o3 o4 o5 : Object

data Designator : Set where
  s1 s2 s3 s4 s5 : Designator
  
module w1 where

  data _inDomain_ : Object → World → Set where
    d12 : o1 inDomain w1  -- док-во, что объект принадлежит домену
    d22 : o2 inDomain w2
    
  data Domain : World → Set where
    dom : {w : World} → (o : Object) → {o inDomain w} → Domain w

  -- мир элемента домена
  world : {w : World} → Domain w → World
  world (dom {w} _) = w

  data _refers-to_in-world_ : Designator → Object → World → Set where
    r111 : s1 refers-to o1 in-world w1
    r112 : s1 refers-to o1 in-world w2
    r113 : s1 refers-to o1 in-world w3
    
  isRigidDesignator : (s : Designator) → {Object} → Set
  isRigidDesignator s {o} = ∀ (w : World) → s refers-to o in-world w

  _ : isRigidDesignator s1
  _ = prf
    where
    prf : ∀ (w : World) → s1 refers-to o1 in-world w
    prf w1 = r111
    prf w2 = r112
    prf w3 = r113


  data RigidDesignator : Set where
    rd : (s : Designator) → {o : Object} → isRigidDesignator s {o} → RigidDesignator


data Subset (A : Set) : Set where
  elem : A → Subset A

-- тип доказательств, что x -- сосед y
data Сосед (A : Set) (x : A) : A → Set where
  да-сосед : (y : A) → Сосед A x y 

a1 : Сосед Nat zero zero
a1 = да-сосед zero 

data Сосед' {A : Set} (x : A) : A → Set where
  да-сосед' : (y : A) → Сосед' x y

a' : Сосед' zero _
a' = да-сосед' zero


module m1 where
  data Суждение : Set where
    J1 J2 J3 : Суждение

  data Контекст : Set where
    ∅   : Контекст
    _,_ : Суждение → Контекст → Контекст
  
  infixr 4 _,_
  
  c1 = ∅
  c2 = J2 , ∅
  c3 = J1 , c1
  c4 = J1 , J2 , J3 , ∅

-- Тип может иметь параметры:

module m2 where

  data Контекст (A : Set) : Set where
    ∅   : Контекст A
    _,_ : A → Контекст A → Контекст A
 
  infixr 4 _,_
  
  data Суждение : Set where
    J1 J2 J3 : Суждение

  КонтекстСуждений = Контекст Суждение

  c1 c2 c3 c4 : КонтекстСуждений
  c1 = ∅
  c2 = J2 , ∅
  c3 = J1 , c1
  c4 = J1 , J2 , J3 , ∅


-- Типы могут быть индексированными.
-- Параметры одни и те же для всех конструкторов, индексы могут отличаться.


-- Пропозициональное равенство --
-- =========================== --

module PropEq where

  data ≡₁ (A : Set) (x : A) : A → Set where
    refl₁ : ≡₁ A x x
    
  data ≡₂ (A : Set) (x : A) : A → Set where
    refl₂ : ≡₂ _ x x
    
  data ≡₃ {A : Set} (x : A) : A → Set where
    refl₃ : ≡₃ x x
    
  data _≡₄_ {A : Set} (x : A) : A → Set where
    refl₄ : x ≡₄ x
    
  data ≡₅ (A : Set) : A → A → Set where
    refl₅ : ∀ (x : A) → ≡₅ A x x
    
  data _≡₆_ {A : Set} : A → A → Set where
    refl₆ : ∀ (x : A) → x ≡₆ x
    


data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
    
_ : предыдущее (suc (suc zero)) ≡ suc zero
_ = refl 

_ : f2 ≡ f3
_ = refl


