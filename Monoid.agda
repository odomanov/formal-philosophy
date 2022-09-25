{-# OPTIONS --cumulativity #-}
module Monoid where

open import Agda.Primitive

open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)
open import Relation.Binary.Structures using (IsEquivalence)
-- record isEquivalence {a} {A : Set a} (_≈_ : A → A → Set) : Set a where
--   field
--     reflexivity : ∀ x → x ≈ x
--     commutativity : ∀ x y → x ≈ y → y ≈ x
--     transitivity  : ∀ x y z → x ≈ y → y ≈ z → x ≈ z

record Monoid {ℓ} : Set (lsuc ℓ) where
  field
    Carrier : Set ℓ
    _≈_ : Carrier → Carrier → Set 
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

  open import Data.Nat
  open import Relation.Binary.PropositionalEquality.Core

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

  open import Relation.Binary.PropositionalEquality 

  id : A → A
  id x = x

  _∘_ : (f g : A → A) → A → A
  f ∘ g = λ x → f (g x)
  
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

open import Data.Empty
open import Data.List
open import Data.Product
open import Data.Unit

FreeMonoid : ∀ {ℓ} (X : Set ℓ) (_≈_ : X → X → Set) (equiv : IsEquivalence _≈_)
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
  _≋_ : List X → List X → Set
  [] ≋ [] = ⊤
  [] ≋ (_ ∷ _) = ⊥
  (_ ∷ _) ≋ [] = ⊥
  (x ∷ xs) ≋ (y ∷ ys) = x ≈ y × xs ≋ ys

  refl' : ∀ {x} → x ≋ x
  refl' {[]} = tt
  refl' {x ∷ xs} = refl  , refl'

  sym' : ∀ {x y} → (x ≋ y) → (y ≋ x)
  sym' {[]} {[]} p = tt
  sym' {[]} {x ∷ y} p = p
  sym' {x ∷ x₁} {x₂ ∷ y} (p1 , p2) = (sym p1) , (sym' p2)

  trans' : ∀ {x y z} → (x ≋ y) → (y ≋ z) → (x ≋ z)
  trans' {[]} {[]} _ p = p
  trans' {[]} {_ ∷ _} ()
  trans' {_ ∷ _} {[]} ()
  trans' {x ∷ xs} {y ∷ ys} {[]} _ p = p
  trans' {x ∷ xs} {y ∷ ys} {z ∷ zs} (p11 , p12) (p21 , p22) =
      (trans p11 p21) , (trans' p12 p22)
  
  equiv' : IsEquivalence _≋_
  equiv' = record { refl = refl' ; sym = sym' ; trans = trans' }

  ul : ∀ x → ([] ++ x) ≋ x
  ul [] = tt
  ul (x ∷ xs) = refl , (ul xs)

  ur : ∀ x → (x ++ []) ≋ x
  ur [] = tt
  ur (x ∷ xs) = refl , (ur xs)

  as : ∀ x y z → ((x ++ y) ++ z) ≋ (x ++ (y ++ z))
  as [] [] [] = tt
  as [] [] (_ ∷ _) = refl , refl'
  as [] (_ ∷ _) [] = refl , refl'
  as [] (_ ∷ _) (_ ∷ _) = refl , refl'
  as (x ∷ xs) y z = refl , as xs y z

