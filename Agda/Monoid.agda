module Monoid where

-- open import Agda.Primitive
open import TTCore

record IsEquivalence {a} {A : Set a} (_≈_ : A → A → Set a) : Set a where
  field
    reflex  : ∀ x → x ≈ x
    sym     : ∀ x y → x ≈ y → y ≈ x
    trans   : ∀ x y z → x ≈ y → y ≈ z → x ≈ z

-- ≡ is equivalence
isEquivalence : ∀ {a} {A : Set a} → IsEquivalence {a} {A} _≡_
isEquivalence = record { reflex = λ x → refl
                       ; sym = sym'
                       ; trans = trans'
                       }
  where
  sym' : ∀ x y → x ≡ y → y ≡ x
  sym' x y refl = refl

  trans' : ∀ x y z → x ≡ y → y ≡ z → x ≡ z
  trans' x y z refl refl = refl
  

record Monoid {ℓ} : Set (lsuc ℓ) where
  field
    Carrier : Set ℓ
    _≈_ : Carrier → Carrier → Set ℓ 
    equiv : IsEquivalence _≈_ 
    _∙_ : Carrier → Carrier → Carrier
    ε   : Carrier
    unitl : ∀ a → (ε ∙ a) ≈ a
    unitr : ∀ a → (a ∙ ε) ≈ a
    assoc : ∀ a b c → (a ∙ b) ∙ c ≈ a ∙ (b ∙ c)

  infix 0 _≈_
  

-- Пример1: ℕ как моноид относительно + и *

module Mℕ+ where

  open import TTCore
  open import Nat

  ul : ∀ n → zero + n ≡ n
  ul n = refl
  
  ur : ∀ n → n + zero ≡ n
  ur zero = refl
  ur (suc n) = cong suc (ur n)

  as : ∀ l m n → (l + m) + n ≡ l + (m + n)
  as zero m n = refl
  as (suc l) m n = cong suc (as l m n)

  MN+ : Monoid
  MN+ = record { Carrier = ℕ
               ; _≈_ = _≡_
               ; equiv = isEquivalence
               ; _∙_ = _+_
               ; ε = zero
               ; unitl = ul
               ; unitr = ur
               ; assoc = as 
               }

-- Пример2: строка как моноид

-- module MString where

--   open import TTCore hiding (_++_; _==_)

--   -- open import Data.Char
--   -- open import Data.List as 𝕃 hiding (_++_)
--   -- open import Data.List.Relation.Binary.Pointwise
--   -- open import Data.String renaming (_++_ to _+++_)
--   open import Data.String.Base using (_++_)
--   open import Data.String.Properties using (_≟_)
--   -- open import Relation.Binary.PropositionalEquality using (T)

--   ul : ∀ a → ("" ++ a ≟ a)
--   ul a = {!Pointwise _≈_!}

--   ur : ∀ a → a ++ "" ≟ a
--   ur a = {!!}

--   as : ∀ a b c → (a ++ b) ++ c ≟ a ++ (b ++ c)
--   as a b c = {!!}

--   MS : Monoid
--   MS = record { Carrier = String
--               ; _≈_ = _≟_
--               ; equiv = ?
--               ; _∙_ = _++_
--               ; ε = ""
--               ; unitl = ul
--               ; unitr = ur
--               ; assoc = as
--               }



-- Пример3 : композиция функций как моноид

module MFunc (A : Set) where

  open import TTCore
  
  ul : (f : A → A) → id ∘ f ≡ f
  ul f = refl

  ur : (f : A → A) → f ∘ id ≡ f
  ur f = refl

  as : (f g h : A → A) → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)
  as f g h = refl

  MF : Monoid 
  MF = record { Carrier = (A → A)
              ; _≈_ = _≡_
              ; equiv = isEquivalence
              ; _∙_ = _∘_ 
              ; ε = id 
              ; unitl = ul
              ; unitr = ur
              ; assoc = as
              }


-- Свободный моноид
-- ================

-- Свободный моноид на типе X это последовательности элементов X с
-- операцией конкатенации и пустой последовательностью как единицей. Будем
-- моделировать последовательности как списки.

open import TTCore
-- open import Data.Empty
-- open import Data.List
-- open import Data.Product
-- open import Data.Unit

FreeMonoid : ∀ {ℓ} (X : Set ℓ) (_≈_ : X → X → Set ℓ) (equiv : IsEquivalence _≈_)
   → Monoid {ℓ}

FreeMonoid {ℓ} X _≈_ equiv = record
                           { Carrier = List X
                           ; _≈_ = _≋_
                           ; equiv = equiv'
                           ; _∙_ = _++_
                           ; ε = []
                           ; unitl = ul
                           ; unitr = ur
                           ; assoc = as
                           }
  where
  open IsEquivalence equiv
  _≋_ : List X → List X → Set ℓ
  [] ≋ [] = Lift ℓ ⊤
  [] ≋ (_ ∷ _) = Lift ℓ ⊥
  (_ ∷ _) ≋ [] = Lift ℓ ⊥
  (x ∷ xs) ≋ (y ∷ ys) = x ≈ y × xs ≋ ys

  refl' : ∀ x → x ≋ x
  refl' [] = lift tt
  refl' (x ∷ xs) = reflex x , (refl' xs)

  sym' : ∀ x y → (x ≋ y) → (y ≋ x)
  sym' [] [] p = lift tt
  sym' [] (x ∷ y) p = p
  sym' (x ∷ x₁) (x₂ ∷ y) (p1 , p2) = (sym x x₂ p1) , sym' x₁ y p2 

  trans' : ∀ x y z → (x ≋ y) → (y ≋ z) → (x ≋ z)
  trans' [] [] _ _ p = p
  trans' [] (_ ∷ _) _ ()
  trans' (_ ∷ _) [] _ ()
  trans' (x ∷ xs) (y ∷ ys) [] _ p = p
  trans' (x ∷ xs) (y ∷ ys) (z ∷ zs) (p11 , p12) (p21 , p22) =
      (trans x y z p11 p21) , trans' xs ys zs p12 p22 
  
  equiv' : IsEquivalence _≋_
  equiv' = record { reflex = refl' ; sym = sym' ; trans = trans' }

  ul : ∀ x → ([] ++ x) ≋ x
  ul [] = lift tt 
  ul (x ∷ xs) = reflex x , ul xs 

  ur : ∀ x → (x ++ []) ≋ x
  ur [] = lift tt 
  ur (x ∷ xs) = reflex x , (ur xs)

  as : ∀ x y z → ((x ++ y) ++ z) ≋ (x ++ (y ++ z))
  as [] [] [] = lift tt 
  as [] [] (z ∷ zs) =  reflex z , refl' zs 
  as [] (y ∷ ys) [] = reflex y , refl' (ys ++ []) 
  as [] (y ∷ ys) (z ∷ zs) = reflex y , refl' (ys ++ z ∷ zs) --refl , refl'
  as (x ∷ xs) y z = reflex x , as xs y z 

