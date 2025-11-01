module _ where

record isEquivalence {A : Set} (_≈_ : A → A → Set) : Set where
  field
    reflexivity : ∀ x → x ≈ x
    commutativity : ∀ x y → x ≈ y → y ≈ x
    transitivity  : ∀ x y z → x ≈ y → y ≈ z → x ≈ z

-- Магма это множество (носитель) с равенством и бинарной операцией, на
-- которую не налагается никаких условий, кроме замкнутости.
record Magma : Set₁ where
  field
    Carrier : Set
    _≈_     : Carrier → Carrier → Set
    equiv   : isEquivalence _≈_
    _∙_     : Carrier → Carrier → Carrier
  infix 4 _≈_
  infix 5 _∙_
  open isEquivalence equiv public


-- Свободная магма на множестве X (с равенством).
-- Пример: слова, составляемые из букв (но порядок составления важен, поэтому
-- это слова со скобками). 

module FreeMagma where

  open import Data.Empty
  open import Data.Product
  open import Data.Unit
  
  FreeMagma : ∀ (X : Set) (_≈_ : X → X → Set) (equiv : isEquivalence _≈_) (_∙_ : X → X → X)
              → Magma
  FreeMagma X _≈_ equiv _∙_ = record { Carrier = C ; _≈_ = _≈ᶠ_ ; equiv = equivᶠ ; _∙_ = _∙ᶠ_ }
    where
    open isEquivalence equiv
    data C : Set where
      atom : X → C
      _∙ᶠ_ : C → C → C
    open C
  
    _≈ᶠ_ : C → C → Set
    atom x ≈ᶠ atom y = x ≈ y
    (x ∙ᶠ x₁) ≈ᶠ (y ∙ᶠ y₁) = (x ≈ᶠ y) × (x₁ ≈ᶠ y₁)
    _ ≈ᶠ _ = ⊥

    reflexivityᶠ : ∀ x → x ≈ᶠ x
    reflexivityᶠ (atom x) = reflexivity x 
    reflexivityᶠ (x ∙ᶠ y) = reflexivityᶠ x , reflexivityᶠ y

    commutativityᶠ : ∀ x y → x ≈ᶠ y → y ≈ᶠ x
    commutativityᶠ (atom x) (atom y) = commutativity x y
    commutativityᶠ (atom _) (_ ∙ᶠ _) p = p
    commutativityᶠ (_ ∙ᶠ _) (atom _) p = p
    commutativityᶠ (x1 ∙ᶠ x2) (y1 ∙ᶠ y2) (p1 , p2) =
      (commutativityᶠ x1 y1 p1) , (commutativityᶠ x2 y2 p2)

    transitivityᶠ : ∀ x y z → x ≈ᶠ y → y ≈ᶠ z → x ≈ᶠ z
    transitivityᶠ (atom x) (atom y) (atom z) = transitivity x y z
    transitivityᶠ (atom _) (atom _) (_ ∙ᶠ _) _ y=z = y=z
    transitivityᶠ (atom _) (_ ∙ᶠ _) _ ()
    transitivityᶠ (_ ∙ᶠ _) (atom _) _ ()
    transitivityᶠ (_ ∙ᶠ _) (_ ∙ᶠ _) (atom _) _ y=z = y=z
    transitivityᶠ (x1 ∙ᶠ x2) (y1 ∙ᶠ y2) (z1 ∙ᶠ z2) (p11 , p12) (p21 , p22) =
      transitivityᶠ x1 y1 z1 p11 p21 , transitivityᶠ x2 y2 z2 p12 p22
    
    equivᶠ : isEquivalence _≈ᶠ_
    equivᶠ = record { reflexivity = λ x → reflexivityᶠ x
                    ; commutativity = λ x y → commutativityᶠ x y
                    ; transitivity = λ x y z → transitivityᶠ x y z
                    }



-- Свободная магма это бинарное дерево (см. Minimalist Program).
-- Ср. с определением бинарного дерева.




-- Полугруппа
-- ==========

-- Полугруппа это магма с ассоциативной операцией.
-- Ассоциативность означает, что порядок операций не важен, поэтому скобки можно опускать.

record Semigroup : Set₁ where
  field
    magma : Magma
  open Magma magma public
  field
    assoc  : ∀ x y z → (x ∙ y) ∙ z ≈ x ∙ (y ∙ z)   -- скобки можно опускать


-- Свободная полугруппа.

-- TODO




-- Моноид
-- ====== 

-- Моноид это полугруппа с единичным (или нейтральным) элементом.

record Monoid : Set₁ where
  field
    semig : Semigroup
  open Semigroup semig
  field
    ε : Carrier
    unitl : ∀ x → ε ∙ x ≈ x          -- аксиомы единичности или нейтральности
    unitr : ∀ x → x ∙ ε ≈ x


-------------------------------------------------------------------------------
-- Любую полугруппу можно превратить в моноид, добавив ε и доопределив _∙_ так,
-- чтобы ∀ x → ε ∙ x ≈ x и ∀ x → x ∙ ε ≈ x
-- Покажем это.
  
module Semigroup→Monoid where

  open import Data.Empty
  open import Data.Unit
  
  S→M : Semigroup → Monoid
  S→M s = record { semig = record { magma = record { Carrier = Carrierₘ
                                                   ; _≈_ = _≈ₘ_
                                                   ; equiv = equivₘ
                                                   ; _∙_ = _∙ₘ_
                                                   }
                                  ; assoc = λ x y z → assocₘ x y z
                                  }
                 ; ε = εₘ
                 ; unitl = λ x → unitlₘ x
                 ; unitr = λ x → unitrₘ x
                 }
    where
    open Semigroup s
    
    -- Расширяем носитель новым элементом εₘ
    data Carrierₘ : Set where
      xₘ : Carrier → Carrierₘ
      εₘ : Carrierₘ
  
    -- новое εₘ отличается от всех старых элементов
    _≈ₘ_ : Carrierₘ → Carrierₘ → Set
    xₘ x ≈ₘ xₘ y = x ≈ y
    εₘ ≈ₘ εₘ = ⊤
    _ ≈ₘ _ = ⊥
  
    -- докажем, что ≈ₘ -- эквивалентность
    reflexivityₘ : ∀ x → x ≈ₘ x
    reflexivityₘ (xₘ x) = reflexivity x
    reflexivityₘ εₘ = tt
    
    commutativityₘ : ∀ x y → x ≈ₘ y → y ≈ₘ x
    commutativityₘ (xₘ x) (xₘ y) x=y = commutativity x y x=y
    commutativityₘ εₘ εₘ x=y = tt
    
    transitivityₘ  : ∀ x y z → x ≈ₘ y → y ≈ₘ z → x ≈ₘ z
    transitivityₘ (xₘ x) (xₘ y) (xₘ z) x=y y=z = transitivity x y z x=y y=z
    transitivityₘ εₘ εₘ εₘ x=y y=z = tt
  
    equivₘ : isEquivalence _≈ₘ_
    equivₘ = record { reflexivity = λ x → reflexivityₘ x
                    ; commutativity = λ x y → commutativityₘ x y
                    ; transitivity = λ x y z → transitivityₘ x y z
                    }
  
    -- доопределяем операцию _∙_
    _∙ₘ_ : Carrierₘ → Carrierₘ → Carrierₘ
    xₘ x ∙ₘ xₘ y = xₘ (x ∙ y)
    xₘ x ∙ₘ εₘ   = xₘ x
    εₘ   ∙ₘ xₘ x = xₘ x
    εₘ   ∙ₘ εₘ   = εₘ
  
    unitlₘ : ∀ x → (εₘ ∙ₘ x) ≈ₘ x
    unitlₘ (xₘ x) = reflexivity x
    unitlₘ εₘ = tt
  
    unitrₘ : ∀ x → (x ∙ₘ εₘ) ≈ₘ x
    unitrₘ (xₘ x) = reflexivity x
    unitrₘ εₘ = tt
  
    assocₘ : ∀ x y z → ((x ∙ₘ y) ∙ₘ z) ≈ₘ (x ∙ₘ (y ∙ₘ z))
    assocₘ (xₘ x) (xₘ y) (xₘ z) = assoc x y z 
    assocₘ εₘ εₘ εₘ = tt
    assocₘ (xₘ x) (xₘ y) εₘ     = reflexivity (x ∙ y)
    assocₘ (xₘ x) εₘ     (xₘ z) = reflexivity (x ∙ z)
    assocₘ (xₘ x) εₘ     εₘ     = reflexivity x 
    assocₘ εₘ     (xₘ y) (xₘ z) = reflexivity (y ∙ z)
    assocₘ εₘ     (xₘ y) εₘ     = reflexivity y 
    assocₘ εₘ     εₘ     (xₘ z) = reflexivity z 


-- О моноидах есть отдельный файл Monoid.agda.


