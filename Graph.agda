-- Графы

module Graph where

open import TTCore 

-- Вспомогательная функция.
-- Упрощённая конкатенация списков. Не проверяется уникальность.
  
-- infixl 5 _++_
  
-- _++_ : ∀ {a} {A : Set a} → List A → List A → List A
-- [] ++ x = x
-- (x ∷ xs) ++ y = x ∷ (xs ++ y) 



-- Простейший способ построения графа: список вершин + список рёбер.

module g1 where

  data Edge (A : Set) : Set where
    _~_  : A → A → Edge A

  record Graph (A : Set) : Set₁ where
    constructor ⟨_,_⟩ 
    field
      vertices : List A
      edges    : List (Edge A)

  infix 2 ⟨_,_⟩


  -- Пример
  
  data V : Set where
    a b c d e f : V

  g : Graph V
  g = ⟨ a ∷ d ∷ [] , a ~ d ∷ a ~ f ∷ d ~ b ∷ [] ⟩




-- Другой способ: Граф как список пар из вершины и связанных с ней вершин.

module g2 where

  Graph = (A : Set) → List (A × List A)


  -- Пример
  
  data V : Set where
    a b c d e f : V

  g = (a ,′ b ∷ d ∷ [])
    ∷ (d ,′ a ∷ c ∷ e ∷ [])
    ∷ (e ,′ [])                 -- изолированная вершина
    ∷ []


  -- Граф с помеченными рёбрами

  postulate
    Label : Set


  LabeledGraph = (A : Set) → List (A × List (A × Label))

  -- или:
  
  LabeledGraph' = (A : Set) → List (A × List A × Label)



-- Дерево -- частный случай графа
-- ============================== 

data Tree (A : Set) : Set where
  leaf : A → Tree A
  tree : A → List (Tree A) → Tree A



-- Более корректное определение
-- ============================

-- Все предыдущие определения допускают рёбра к несуществующим вершинам.


-- Алгебраические графы.
-- См. https://dl.acm.org/doi/10.1145/3122955.3122956
-- Библиотека на Haskell: http://hackage.haskell.org/package/algebraic-graphs
-- Библиотека на Agda: https://github.com/algebraic-graphs/agda


module g3 where

  data Graph (A : Set) : Set where
    empty  : Graph A
    vertex : A → Graph A
    _+_    : Graph A → Graph A → Graph A
    _*_    : Graph A → Graph A → Graph A

  infixl 8 _+_
  infixl 9 _*_

  

  -- граф вида  ∙ → ∙ 
  edge : ∀ {A} → A → A → Graph A
  edge a b = (vertex a) * (vertex b)

  -- изолированные вершины
  vertices : ∀ {A} -> List A -> Graph A
  vertices [] = empty
  vertices (x ∷ xs) = vertex x + vertices xs

  -- построение графа из списка рёбер
  edges : ∀ {A} -> List (A × A) -> Graph A
  edges [] = empty
  edges (x ∷ xs) = edge (proj₁′ x) (proj₂′ x) + edges xs

  -- построение графа из вершин и рёбер
  graph : ∀ {A} -> List A -> List (A × A) -> Graph A
  graph vs es = (vertices vs) + (edges es)

  -- Извлечение вершин
  Graph→Vertices : ∀ {A} → Graph A → List A
  Graph→Vertices empty = []
  Graph→Vertices (vertex x) = x ∷ []
  Graph→Vertices (x + y) = Graph→Vertices x ++ Graph→Vertices y
  Graph→Vertices (x * y) = Graph→Vertices x ++ Graph→Vertices y


  -- УПРАЖНЕНИЕ: написать функцию Graph→Edges (извлечения рёбер).


  -- Подграф
  _⊆_ : ∀ {A} -> Graph A -> Graph A -> Set
  x ⊆ y = x + y ≡ y



-- Algebraic graphs are characterised by the following 8 axioms:
--   + is commutative and associative, i.e. x + y = y + x and x + (y + z) = (x + y) + z.
--   (G,→, ε ) is a monoid, i.e. ε → x = x, x → ε = x and x → (y → z) = (x →y) → z.
--   → distributes over +: x → (y + z) = x → y + x → z and (x + y) → z = x → z + y → z.
--   Decomposition: x →y → z = x →y + x → z + y → z.


module g4 where

  -- Алгебра графов

  record GraphAlgebra : Set₁ where
    field
      G     : Set
      empty : G
      _+_   : G → G → G
      _*_   : G → G → G
      _≈_   : G → G → Set
    infix 4 _≈_
    infixl 8 _+_
    infixl 9 _*_
    field
      +comm    : ∀ x y   → x + y ≈ y + x
      +assoc   : ∀ x y z → x + (y + z) ≈ (x + y) + z 
      *idl     : ∀ x     → empty * x ≈ x
      *idr     : ∀ x     → x * empty ≈ x
      *assoc   : ∀ x y z → x * (y * z) ≈ (x * y) * z
      distrib1 : ∀ x y z → x * (y + z) ≈ x * y + x * z
      distrib2 : ∀ x y z → (x + y) * z ≈ x * z + y * z
      decomp   : ∀ x y z → x * y * z ≈ x * y + x * z + y * z



  -- Добавим семантику

  -- Тип графов в обычном смысле (список вершин + список рёбер)
  data Gr (A : Set) : Set where
    gr : List A → List (A × A) → Gr A

  empty : ∀ {A} → Gr A
  empty = gr [] []

  vertex : ∀ {A} → A → Gr A
  vertex x = gr (x ∷ []) []


  -- Постулируем равенство, учитывающее перестановки и уникальность.

  infix 4 _≡L_
  
  postulate
    _≡L_ : ∀ {a} {A : Set a} → List A → List A → Set
    ≡L-refl : ∀ {a} {A : Set a} (x : List A) → x ≡L x
    ≡L-symm : ∀ {a} {A : Set a} (x y : List A) → x ++ y ≡L y ++ x
    
  _≈_ : ∀ {A} → Gr A → Gr A → Set
  gr v1 e1 ≈ gr v2 e2 = (v1 ≡L v2) × (e1 ≡L e2)

  -- Определяем операции на Gr A
  
  _+_ : ∀ {A} → Gr A → Gr A → Gr A
  gr x1 y1 + gr x2 y2 = gr (x1 ++ x2) (y1 ++ y2)

  _*_ : ∀ {A} → Gr A → Gr A → Gr A
  gr [] _ * g = g  
  g * gr [] _ = g  
  _*_ {A} (gr v1 e1) (gr v2 e2) =  gr (v1 ++ v2) (e1 ++ e2 ++ (δe v1 v2))
    where
    1* : A → List A → List (A × A)
    1* x [] = []
    1* x (y ∷ ys) = (x , y) ∷ 1* x ys

    δe : List A → List A → List (A × A)
    δe [] _ = []
    δe (x ∷ xs) ys = 1* x ys ++ δe xs ys


  -- можно было бы включить эти операции в определение типа как конструкторы:
  data Gr' (A : Set) : List A → List (A × A) → Set where
    empty'  : Gr' A [] []
    vertex' : ∀ x → Gr' A (x ∷ []) []
    _+'_    : ∀ {v1 v2 e1 e2}
              → Gr' A v1 e1
              → Gr' A v2 e2
              → Gr' A (v1 ++ v2) (e1 ++ e2)


  -- УПРАЖНЕНИЯ: допишите _*'_, а также функции извлечения вершин и рёбер из графов Gr'.


  g+comm : ∀ {A} (x y : Gr A) → (x + y) ≈ (y + x)
  g+comm (gr v1 e1) (gr v2 e2) = (≡L-symm v1 v2) , (≡L-symm e1 e2)

  g*idl : ∀ {A} (x : Gr A) → (empty * x) ≈ x
  g*idl (gr v e) = ≡L-refl v , ≡L-refl e 

  -- g : ∀ {A} → GraphAlgebra 
  -- g {A} = ?


  -- GraphAlgebra это теория графов.
  -- Но при конструктивном подходе (Gr) мы _сразу_ строим модель.
  -- И лишь затем доказываем аксиомы.
