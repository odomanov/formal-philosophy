module Monoid where

record Monoid : Set₁ where
  field
    Carrier : Set
    _≈_ : Carrier → Carrier → Set
    _∙_ : Carrier → Carrier → Carrier
    ε   : Carrier
    unitl : ∀ a → (ε ∙ a) ≈ a
    unitr : ∀ a → (a ∙ ε) ≈ a
    assoc : ∀ a b c → (a ∙ b) ∙ c ≈ a ∙ (b ∙ c)
    -- equiv : isEquivalence _≈_ 

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
               ; _∙_ = _+_
               ; ε = zero
               ; unitl = ul
               ; unitr = ur
               ; assoc = as 
               }

-- Пример2: строка как моноид

module MString where

  open import TTCore hiding (_++_; _==_)

  -- open import Data.Char
  -- open import Data.List as 𝕃 hiding (_++_)
  -- open import Data.List.Relation.Binary.Pointwise
  -- open import Data.String renaming (_++_ to _+++_)
  open import Data.String.Base using (_++_)
  open import Data.String.Properties using (_≟_)
  -- open import Relation.Binary.PropositionalEquality using (T)

  ul : ∀ a → ("" ++ a ≟ a)
  ul a = {!Pointwise _≈_!}

  ur : ∀ a → a ++ "" ≟ a
  ur a = {!!}

  as : ∀ a b c → (a ++ b) ++ c ≟ a ++ (b ++ c)
  as a b c = {!!}

  MS : Monoid
  MS = record { Carrier = String
              ; _≈_ = _≟_
              ; _∙_ = _++_
              ; ε = ""
              ; unitl = ul
              ; unitr = ur
              ; assoc = as
              }

