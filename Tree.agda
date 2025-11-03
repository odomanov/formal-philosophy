-- Тип деревьев

-- TODO: traverse, свойства

open import TTCore

module _ where

-- бинарное дерево
data Tree (A : Set) : Set where
  ⟪_⟫   : A → Tree A
  ⟦_-_⟧ : Tree A → Tree A → Tree A

data _connects_ : {A : Set} → Tree A → Tree A → Set where
  c0  : {A : Set} {x : Tree A} → x connects x
  _cl : {A : Set} {x0 x1 x2 : Tree A} → x0 connects ⟦ x1 - x2 ⟧ → x0 connects x1
  _cr : {A : Set} {x0 x1 x2 : Tree A} → x0 connects ⟦ x1 - x2 ⟧ → x0 connects x2

path_to_ : {A : Set} → Tree A → Tree A → Set
path x0 to x = x0 connects x


module ex1 where

  a1 = ⟪ "a1" ⟫
  a2 = ⟪ "a2" ⟫
  
  T1 : Tree String
  T1 = ⟦ a1 - a2 ⟧
  
  b1 = ⟪ "b1" ⟫
  b2 = ⟪ "b2" ⟫
  
  T2 = ⟦ a1 - ⟦ b1 - b2 ⟧ ⟧
  
  _ : path T2 to b2
  _ = c0 cr cr
  
  T2' = ⟦ a1
        - ⟦ b1
          - b2 ⟧ ⟧
  
  
  pattern _∙_ x y = ⟦ x - y ⟧
  
  T3 = a1 ∙ (b1 ∙ b2)
  
  _ : T2 ≡ T3
  _ = refl
  
  
  T5 = a1 ∙ ((a2 ∙ b1) ∙ b2)
  
  _ : path T5 to b1
  _ = c0 cr cl cr
  
  T5' = a1
        ∙ ((a2
            ∙ b1)
           ∙ b2)
  


--  продолжить ...
