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





-- Пример. Возможные миры.
-- =======================

data World : Set where
  w1 w2 w3 : World

data Object : Set where
  o1 o2 o3 o4 o5 : Object

data Designator : Set where
  s1 s2 s3 s4 s5 : Designator
  

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

s1rd : isRigidDesignator s1
s1rd = prf
  where
  prf : ∀ (w : World) → s1 refers-to o1 in-world w
  prf w1 = r111
  prf w2 = r112
  prf w3 = r113


-- тип жёстких десигнаторов
data RigidDesignator : Set where
  rd : (s : Designator) → {o : Object} → isRigidDesignator s {o} → RigidDesignator


fs : RigidDesignator → Designator 
fs (rd s _) = s

fo : RigidDesignator → Object
fo (rd _ {o} _) = o

fp : (r : RigidDesignator) → isRigidDesignator (fs r) {fo r}
fp (rd _ p) = p

-------------------------------------------------------



-- Параметризованные типы --
-- ====================== --


module m1 where
  data Слово : Set where
    w1 w2 w3 : Слово

  data Список : Set where
    ∅   : Список
    _,_ : Слово → Список → Список
  
  infixr 4 _,_
  
  Сп1 = ∅
  Сп2 = w2 , ∅
  Сп3 = w1 , Сп1
  Сп4 = w1 , w2 , w3 , ∅
  Сп5 = w1 , (w2 , (w3 , ∅))


-- Тип может иметь параметры:

module m2 where

  data Список (A : Set) : Set where
    ∅   : Список A
    _,_ : A → Список A → Список A
 
  -- Отличие параметров от индексов:
  -- Параметры одни и те же для всех конструкторов, индексы могут отличаться.

  infixr 4 _,_
  
  data Слово : Set where
    w1 w2 w3 : Слово

  СписокСлов = Список Слово

  Сп1 Сп2 Сп3 Сп4 : СписокСлов
  Сп1 = ∅
  Сп2 = w2 , ∅
  Сп3 = w1 , Сп1
  Сп4 = w1 , w2 , w3 , ∅


  хвост : ∀ {A} → Список A → Список A
  хвост ∅ = ∅
  хвост (_ , x) = x

  -- Для извлечения первого слова нужно усложнение.

  неПуст : ∀ {A} → Список A → Set
  неПуст ∅ = ⊥
  неПуст _ = ⊤

  первый : ∀ {A} → (сп : Список A) → {неПуст сп} → A
  первый (x , _) = x





-- Пропозициональное равенство --
-- =========================== --

module PropEq where

  -- предикат Eq A x y
  data Eq (A : Set) (x : A) : A → Set where
    refl-eq : Eq A x x                       -- _вообще говоря_ разное для разных x
    
  data ≡₁ (A : Set) (x : A) : A → Set where
    refl₁ : ≡₁ A x x
    
  data ≡₂ (A : Set) (x : A) : A → Set where
    refl₂ : ≡₂ _ x x
    
  data ≡₃ {A : Set} (x : A) : A → Set where
    refl₃ : ≡₃ x x
    
  data _≡_ {A : Set} (x : A) : A → Set where
    refl : x ≡ x


  data ≡₅ (A : Set) : A → A → Set where
    refl₅ : ∀ x → ≡₅ A x x                 -- явная зависимость от x
    
  data _≡₆_ {A : Set} : A → A → Set where
    refl₆ : ∀ x → x ≡₆ x
    


data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x


_ : предыдущее (suc (suc zero)) ≡ suc zero
_ = refl 

_ : f2 ≡ f3
_ = refl



-- Свойства равенства

reflex : ∀ {A} {x : A} → x ≡ x
reflex = refl

sym : ∀ {A} {x y : A} → x ≡ y → y ≡ x
sym refl = refl                              -- Это разные refl !!

trans : ∀ {A} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl


-- Подстановка

subst : ∀ {A} (P : A → Set) {x y : A} → x ≡ y → P x → P y
subst P refl px = px
