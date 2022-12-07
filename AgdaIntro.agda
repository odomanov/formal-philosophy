-- Agda. Очень краткое введение
-- ============================

-- Два дефиса (как в начале этой строки) обозначают комментарий: они и всё,
-- что написано до конца строки не видно программе.
-- Многострочные комментарии заключаются между {- и -} (см. ниже).
-- Если вы нажмёте в Emacs Ctrl-c Ctrl-l, то текущий файл обработается и появится
-- расцветка, в которой комментарии будут сразу видны.

-- Полная документация: https://agda.readthedocs.io/en/v2.6.0/.
-- (нам нужна не последняя версия!).
-- Там же есть список учебников:
-- https://agda.readthedocs.io/en/latest/getting-started/tutorial-list.html.


-- Программа Агды состоит из деклараций, записанных в файл с расширением '.agda'
-- (как этот).
-- Программа разбивается на модули.
-- Модуль содержит определения и вычисления, которые не видны вне модуля.
-- Их можно сделать видимыми, открыв модуль командой 'open' (см. ниже).
-- Каждый файл должен содержать главный модуль, имя которого совпадает с именем файла:


module AgdaIntro where                     -- начало модуля AgdaIntro


-- Выражения языка Agda состоят из синтаксических единиц (слов,
-- операторов,...) разделённых пробелами (кроме скобок и точки с запятой,
-- которые не требуют пробелов).  Длинные выражения могут быть продолжены на
-- следующей строке, если она содержит отступ.  Отступы часто
-- отмечают смысловые блоки.

-- Типы в Агде сами являются элементами универсума типов, который обозначаются Set.
-- Имеется иерархия универсумов Set₀, Set₁,..., которые также можно записывать
-- как Set0, Set1,... или Set ℓ, где ℓ -- уровень универсума, относящийся к типу Level.
-- Нижний универсум Set₀ пишется также как просто Set.
-- Универсумы называются также сортами.

-- Agda определяет несколько базовых типов, таких как строки, алфавитные символы и пр.
-- Единственный встроенный сложный тип это тип функций.


-- Тип функций 
-- ===========

{- Тип функций может записываться многими способами:

   (x : A) → B  или A → B                   - основной способ
   ∀ (x : A) → B  
   ∀ x → B  
   (x y : A) → B или A → A → B
   (x : A) → (y : B) → C или A → B → C
   (x : A) (y : B) → C
   ∀ (x : A) (y : B) → C
   ∀ x y → C

   Термы этого типа (то есть функции) также записываются многими способами:
   λ (x : A) → b                            - основной способ
   \ (x : A) → b
   λ x → b
   λ (x y : A) → b

   Применение функции к аргументам, т.е. f(a,b), записывается как f a b.
   
-}



-- Определения новых типов
-- =======================

-- Новые типы определяются инструкцией data.
-- Тип определяется конструкторами, то есть, функциями, конструирующими термы
-- определяемого типа.

-- Например:
-- Тип истинностных значений:
data Bool : Set where               -- декларация типа (он относится к универсуму Set)
  true  : Bool                      -- конструкторы типа (в данном случае -- нуль-местные
  false : Bool                      --                    функции)

-- Другой пример:
-- Тип натуральных чисел:    
data ℕ : Set where
  zero : ℕ                      -- начальное число
  suc  : ℕ → ℕ                  -- следующее число, одноместная функция


-- Как видно, конструкторы имеют тип в качестве области значения. То есть они
-- конструируют элементы типа.

-- Ещё примеры:
-- всегда истинный тип
data ⊤ : Set where
  tt : ⊤

-- пустой тип -- у него нет конструкторов
data ⊥ : Set where


-- Определения функций
-- ===================

-- Функции определяются двумя способами.
-- В первом способе указывается действие функции на все конструкторы её аргументов.
-- Например, определим сложение чисел:

plus : ℕ → ℕ → ℕ                       -- Сначала декларируется тип функции
plus zero    zero    = zero            -- Затем указывается значение на всех возможных
plus zero    (suc n) = suc n           -- конструкторах типа ℕ
plus (suc n) zero    = suc n 
plus (suc n) (suc m) = suc (plus n (suc m))

-- Строго говоря, в определении могут стоять не конструкторы, а шаблоны (patterns).
-- Например, шаблон _ обозначает "неважно какое значение", а любой идентификатор, не являющийся
-- конструктором, считается переменной. Поэтому определение выше можно было бы записать и так:

plus' : ℕ → ℕ → ℕ
plus' zero    n       = n               -- здесь n -- переменная
plus' (suc n) zero    = suc n 
plus' (suc n) (suc m) = suc (plus n (suc m))

-- Или даже так
-- (подчерки в имени обозначают инфиксное употребление; т.е. применение функции к своим
-- аргументам можно написать как '_+_ m n', но можно и как 'm + n'):

_+_ : ℕ → ℕ → ℕ            
zero  + n = n
suc n + m = suc (n + m)


-- Ещё пример функции.
-- Функция f = x + 2
f : ℕ → ℕ
f zero = suc (suc zero)           -- f(0) = 2
f (suc n) = suc (suc (suc n))     -- f(n) = n + 2

-- В данном конкретном случае можно было проще:
f' : ℕ → ℕ
f' n = suc (suc n)

-- Запись определения функций это частный случай определения термов.  При их определении
-- также сначала декларируется тип терма, а затем указывается, чему терм равен.
-- Например:

a : ℕ
a = f zero              -- В данном случае не обязательно декларировать a : ℕ и b : ℕ.

b = f (suc zero)        -- Агда сама определит тип a и b.


-- В Emacs C-c C-n  вычисляет значение (нормализует).  Так можно посмотреть значения a и b.

c = b + a

-- Посмотрите значение c с помощью C-c C-n.

-- Ещё функция:
_≤_ : ℕ → ℕ → Bool
zero ≤ n = true
suc n ≤ zero = false
suc n ≤ suc m = n ≤ m

-- Аргумент функции может быть неявным. Тогда он записывается в фигурных скобках:
-- {x : A} → B
-- ∀ {x} → B
-- Неявные аргументы могут не употребляться при применении функции. Тогда Агда должна
-- вычислить их сама.

-- Например, рассмотрим полиморфную функцию (т.е. ту, которую можно применять к
-- разным типам):
if_then_else_ : {A : Set} → Bool → A → A → A
if false then x else y = y
if true  then x else y = x

-- Аргумент A является неявным и его можно не указывать:

d = if (a ≤ b) then zero else (suc zero)

-- Здесь A = ℕ, но оно не указано -- Агда его вычисляет из типов zero и
-- suc zero.

-- (посмотрите, чему равно d)

-- Ещё примеры скрытых аргументов

id : (A : Set) → A → A              -- Аргумент A явно указан.
id A x = x

id′ : (A : Set) → A → A
id′ _ x = x                         -- Но Агда может его вычислить.

id′′ : {A : Set} → A → A            -- Поэтому можно сделать его неявным.
id′′  x = x


typeOf : {A : Set} (x : A) → Set
typeOf {A} x = A

-- Проверить нормализацию typeOf (С-c C-n)



-- Другой способ определения функций --- применением конструктора функций,
-- встроенного в Agda:

f1 : ℕ → ℕ                         -- декларируется тип функции 
f1 = λ (n : ℕ) → suc (suc n)       -- указывается, чему она равна

f2 = \ (n : ℕ) → suc (suc n)       -- иногда тип можно не декларировать
f3 = λ n → suc (suc n)
f4 = \ (n : ℕ) → n + (suc (suc zero))
f5 = λ (n : ℕ) → n + (suc (suc zero))

-- То же, но определение по шаблонам.  Тогда тип требуется декларировать.
-- Агда сама не может определить тип n.
f6 : ℕ → ℕ
f6 n = suc (suc n)


-- Эти два способа можно комбинировать:

f7 : ℕ → Bool
f7 = λ {  zero   → true
       ; (suc n) → false
       }



-- Из конструированных термов (на самом деле, шаблонов) можно извлекать информацию:
предыдущее : ℕ → ℕ
предыдущее zero = zero
предыдущее (suc n) = n     -- n "извлечено" из suc n


-- Рассмотрим теперь пример функции в зависимый тип.
-- Пример будет находиться в отдельном модуле.

module m3 where                   -- Содержимое модуля пишется ниже с отступом.
                                  -- Главный модуль выше не требует отступов.

  data Страна : Set where
    Япония : Страна
    Буркина-Фасо : Страна

  -- индексированный тип (см. ниже)
  -- Это зависимый тип (тип Город зависит от типа Страна).
  data Город : Страна → Set where
    Токио        : Город Япония
    Саппоро      : Город Япония
    Уагадугу     : Город Буркина-Фасо
    Бобо-Диуласо : Город Буркина-Фасо
  
  столица : (x : Страна) → Город x   -- как видно, тип значения зависит от аргумента 
  столица Япония = Токио
  столица Буркина-Фасо = Уагадугу

  -- другие способы записать эту функцию:
  
  столица' : ∀ (x : Страна) → Город x
  столица' = столица
  
  столица'' : ∀ (x : _) → Город x
  столица'' = столица
  
  столица''' : ∀ x → Город x
  столица''' = столица 

  столица'''' : ∀ (x y : Страна) → Город x
  столица'''' x y = столица x

-- здесь модуль m3 заканчивается (т.к. в следующей строке нет отступа).




-- Параметризованные типы (типы с параметрами) 
-- =========================================== 

-- Начнём с типа без параметров. Определим тип слов и тип списка слов.

module m1 where

  data Слово : Set where
    w1 w2 w3 : Слово

  data Список : Set where
    []  : Список                      -- пустой список 
    _∷_ : Слово → Список → Список     -- добавление слова к списку
  
  infixr 4 _∷_        -- ассоциация справа, т.е. x ∷ y ∷ z = x ∷ (y ∷ z)

  -- Примеры списков:
  Сп1 = []
  Сп2 = w2 ∷ []
  Сп3 = w1 ∷ Сп1
  Сп4 = w1 ∷  w2 ∷  w3 ∷ []
  Сп5 = w1 ∷ (w2 ∷ (w3 ∷ []))    -- равно Сп4 из-за infixr


-- Если мы теперь хотим иметь список не только для слов, а для любых типов,
-- то можем определить его как тип с параметром:

module m2 where

  -- список термов типа A
  data Список (A : Set) : Set where
    []  : Список A
    _∷_ : A → Список A → Список A
 
  infixr 4 _∷_
  
  data Слово : Set where
    w1 w2 w3 : Слово

  СписокСлов = Список Слово

  Сп1 Сп2 Сп3 Сп4 : СписокСлов
  Сп1 = []
  Сп2 = w2 ∷ []
  Сп3 = w1 ∷ Сп2
  Сп4 = w1 ∷ w2 ∷ w3 ∷ []


  СписокЧисел = Список ℕ

  Спч = zero ∷ suc (suc zero) ∷ zero ∷ []


  -- Некоторые вычисления со списками.
  
  хвост : ∀ {A} → Список A → Список A
  хвост [] = []
  хвост (_ ∷ x) = x

  -- Для извлечения первого элемента списка нужно усложнение, поскольку в
  -- пустом списке нет первого элемента.

  -- Предикат "список не пуст".
  неПуст : ∀ {A} → Список A → Set
  неПуст [] = ⊥
  неПуст _  = ⊤

  -- Тогда функция 'первый' применима только к непустым спискам.
  первый : ∀ {A} → (сп : Список A) → {_ : неПуст сп} → A
  первый (x ∷ _) = x            -- Агда понимает, что [] здесь невозможно

  sub : ∀ (A : Set) → Список A → A → Список A
  sub A [] x = []
  sub A (x ∷ l) a = a ∷ l

  sub2 : ∀ (A : Set) → Список A → A → Список A
  sub2 A [] x = []
  sub2 A (x ∷ []) y = x ∷ []
  sub2 A (x ∷ y ∷ z) w = x ∷ w ∷ z


-- Тип списков определён в Agda.Builtin.List следующим образом:

data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A   -- = A → List A → List A

-- Как видно, здесь A может относиться к любому универсуму Set a.


-- УПРАЖНЕНИЕ: написать функцию конкатенации списков:
--   _++_ : ∀ {a} {A : Set a} → List A → List A → List A




-- Индексированные типы
-- ====================


-- Предикаты можно задавать индексированными типами.

-- Здесь Even n это пропозиция "n чётно".
-- Мы задаём конструктор для всех (чётных) n : ℕ.
data Even : ℕ → Set where
  even-zero  : Even zero                              -- док-во, что zero чётно 
  even-plus2 : {n : ℕ} → Even n → Even (suc (suc n))  -- док-во, что n + 2 чётно, если n чётно

-- Отличие индексов от параметров: параметры одни и те же для всех
-- конструкторов, индексы же могут отличаться.
-- Кроме того, параметры связаны во всех конструкторах, а индексы -- нет, 
-- соответствующие переменные должны присутствовать в аргументах конструкторов.


p : Even zero      -- p это доказательство того, что zero чётно.
p = even-zero

-- Чтобы не придумывать имена для доказательств, их можно в таких случаях
-- заменять подчерком.

_ : Even (suc (suc zero))
_ = even-plus2 even-zero

_ : Even (suc (suc (suc (suc (suc (suc zero))))))
_ = even-plus2 (even-plus2 (even-plus2 even-zero)) 

_ : Even _   -- Агда сама подставляет что-то вместо подчерка. Но мы не знаем что.
_ = even-plus2 (even-plus2 (even-plus2 even-zero)) 


-- Другой способ задания предикатов -- через функцию в Set:

_is-even : ℕ → Set
zero is-even = ⊤
(suc (suc n)) is-even = n is-even
_ is-even = ⊥           -- для остальных n нет доказательства чётности


-- Проверить нормализацию  is-even



-- Ещё один индексированный тип -- тип чисел, меньших n:

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} (i : Fin n) → Fin (suc n)

-- Fin n содержит n элементов.
-- Например, Fin zero не имеет конструкторов, т.е. он пуст.



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
  dom : (w : World) → (o : Object) → {_ : o inDomain w} → Domain w

-- УПРАЖНЕНИЕ: переписать нижеследующее, изменив определение на:                  ???
-- data Domain : World → Set where
--   dom : (w : World) → (o : Object) → Domain w


-- мир элемента домена
world : {w : World} → Domain w → World
world (dom w _) = w

world' : {w : World} → Domain w → World
world' {w} _ = w


-- предикат "x refers to y in the world w"
data _refers-to_in-world_ : Designator → Object → World → Set where
  r111 : s1 refers-to o1 in-world w1
  r112 : s1 refers-to o1 in-world w2
  r113 : s1 refers-to o1 in-world w3

-- По-хорошему, _refers-to_in-world_ должен иметь параметром {_ : o inDomain w}.
-- Но мы упрощаем.
-- Кроме того, это определение не гарантирует единственность объекта, на который
-- ссылается Designator.

isRigidDesignator : (s : Designator) → {_ : Object} → Set
isRigidDesignator s {o} = ∀ (w : World) → s refers-to o in-world w

-- Вообще-то, это следовало бы определять через Σ-тип:
-- isRigidDesignator s = Σ[ o ∈ Object ] ∀ (w : World) → s refers-to o in-world w
-- Но у нас ещё нет Σ-типа.

s1rd : isRigidDesignator s1
s1rd = prf
  where
  prf : ∀ (w : World) → s1 refers-to o1 in-world w
  prf w1 = r111
  prf w2 = r112
  prf w3 = r113

-- Другой способ записи
s1rd' : isRigidDesignator s1
s1rd' w1 = r111
s1rd' w2 = r112
s1rd' w3 = r113


-- тип жёстких десигнаторов
data RigidDesignator : Set where
  rd : (s : Designator) → {o : Object} → isRigidDesignator s {o} → RigidDesignator

-- Т.о. все жёсткие десигнаторы имеют вид: rd s p


-- извлечение информации из rd

fs : RigidDesignator → Designator 
fs (rd s _) = s

fo : RigidDesignator → Object
fo (rd _ {o} _) = o

fp : (r : RigidDesignator) → isRigidDesignator (fs r) {fo r}
fp (rd _ p) = p

-------------------------------------------------------



-- Принципы индукции
-- =================

-- Каждому определённому командой data типу соответствует принцип индукции.
-- Он гласит: если известно действие некоторой функции на каждый конструктор типа,
-- то известно действие этой функции на этот тип вообще.

-- Например, принцип индукции для Bool:
-- (здесь строка с дефисами это комментарий, она написана для красоты и не
-- является частью программы)
Bool-induction : (C : Bool → Set)
                 → C false
                 → C true
                 --------------------       
                 → (b : Bool) → C b
Bool-induction C x y false = x
Bool-induction C x y true  = y



-- Принцип индукции для ℕ.
-- Это "принцип математической индукции".
ℕ-ind : (C : ℕ → Set)
        → C zero
        → (∀ {n} → C n → C (suc n))
        ---------------------------
        → (∀ m → C m)
ℕ-ind _ z _  zero   = z
ℕ-ind C z f (suc n) = f (ℕ-ind C z f n)



-- Пропозициональное равенство 
-- =========================== 

-- Рассмотрим разные способы определения равенства.
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
    

-- Так определено в Агде (почти):

infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

-- Здесь refl имеет скрытые параметры, среди которых x. Т.е. refl, вообще-то,
-- выглядит так: refl {a} {A} {x}.


_ : предыдущее (suc (suc zero)) ≡ suc zero
_ = refl 

_ : f2 ≡ f1
_ = refl


-- Принцип индукции для равенства.

≡-induction : ∀ {a} {A : Set a} {C : {x y : A} → x ≡ y → Set a}
            → ((x : A) → C refl)
            -------------------------------
            → (x y : A) (p : x ≡ y) → C p
≡-induction f x _ refl = f x



-- Свойства равенства

reflexivity : ∀ {a} {A : Set a} {x : A} → x ≡ x
reflexivity = refl

symmetry : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
symmetry refl = refl                              -- Это разные refl !!

transitivity : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
transitivity refl refl = refl


-- Подстановка (в HoTT называется transport)

subst : ∀ {a} {A : Set a} {x y : A} (P : A → Set) → x ≡ y → P x → P y
subst P refl px = px


-- Записи
-- ======

-- Тип записей (record) это тип с одним конструктором, в котором аргументы
-- конструктора (поля, fields) поименованы. Его можно рассматривать как
-- таблицу. Соответственно, термы этого типа представляют собой
-- строки таблицы, а поля -- названия столбцов.

-- Рассмотрим пример.

open import Agda.Builtin.String        -- тип строк

record Книга : Set where
  constructor mkBook               -- Конструктор для типа Книга. Не обязателен.
  field
    Автор : String
    Название : String
    НаМесте? : Bool

-- создадим пару термов этого типа

ВиМ : Книга
ВиМ = mkBook "Л.Н.Толстой" "Война и мир" true

ПиН : Книга
ПиН = mkBook "Ф.М.Достоевский" "Преступление и наказание" false

-- Если есть запись (т.е. элемент типа записей), то поля позволяют
-- извлекать из них информацию.

ВиМ-Автор = Книга.Автор ВиМ

ПиН-Название = Книга.Название ПиН

-- Таким образом, поля являются функциями, аргументом которых является
-- запись, а значением -- соответствующее поле (столбец таблицы).
-- Чтобы эти функции были доступны без префикса 'Книга.', запись нужно
-- открыть (таким образом, каждому типу record соответствует модуль с тем
-- же именем):

open Книга

-- Тогда можно писать:

ВиМ-Название = Название ВиМ

ПиН-НаМесте? = НаМесте? ПиН



-- Другой способ создания термов, при котором конструктор (mkBook) не используется
-- и поэтому может отсутствовать в определении типа Книга.

РиЛ : Книга
РиЛ = record { Автор = "А.С.Пушкин"; Название = "Руслан и Людмила"; НаМесте? = true } 

-- часто это пишут так (для красоты):
РиЛ' : Книга
РиЛ' = record { Автор    = "А.С.Пушкин"
              ; Название = "Руслан и Людмила"
              ; НаМесте? = true
              } 


-- record часто используется в определениях.  Например, Σ-тип:

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁        -- в декларации поля могут использоваться предыдущие поля

infixr 4 _,_

-- Это разворачивается в определения (без учёта модуля, соответствующего record):

data Σ' (A : Set) (B : A → Set) : Set where
  _,_ : (a : A) (b : B a) → Σ' A B

proj₁ : {A : Set} {B : A → Set} → Σ' A B → A
proj₁ (a , _) = a

proj₂ : {A : Set} {B : A → Set} → (σ : Σ' A B) → B (proj₁ σ) 
proj₂ (_ , b) = b


-- Пример: список термов разных типов (в отличие от List, в котором термы
-- должны быть одного типа). В частности, типы могут зависеть друг
-- от друга.
postulate
  X : Set
  Y : X → Set
  Z : (x : X) → Y x → Set
  α : X
  β : Y α
  γ : Z α β

-- "нарастающие" Σ-мы
_ : Σ X (λ x → Σ (Y x) (λ y → Z x y))
_ = α , β , γ
  
-- Введём обозначение:

syntax Σ A (λ x → B) = Σ[ x ∈ A ] B


-- Тогда "нарастание" Σ более наглядно:

_ : Σ[ x ∈ X ] Σ[ y ∈ Y x ] Z x y
_ = α , β , γ
  

-- Другой способ определения этого кортежа

record R : Set where
  constructor [_,_,_]
  field
    xx : X
    yy : Y xx
    zz : Z xx yy

_ : R
_ = [ α , β , γ ]

