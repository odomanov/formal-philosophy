module Order where

open import Agda.Builtin.Equality
open import TTCore

Rel : Set → Set1
Rel A = A → A → Set 

record Equiv {A} (_≈_ : Rel A) : Set where
  field
    reflexivity  : ∀ x → x ≈ x
    transitivity : ∀ x y z → x ≈ y → y ≈ z → x ≈ z
    symmetry     : ∀ x y → x ≈ y → y ≈ x
    
    
record PreOrder {A} (_≤_ : Rel A) : Set where
  field
    reflexivity  : ∀ x → x ≤ x
    transitivity : ∀ x y z → x ≤ y → y ≤ z → x ≤ z
    
record PartialOrder {A} (_≈_ : Rel A) (_≤_ : Rel A) : Set where
  field
    reflexivity  : ∀ x → x ≤ x
    transitivity : ∀ x y z → x ≤ y → y ≤ z → x ≤ z
    antisymmetry : ∀ x y → x ≤ y → y ≤ x → x ≈ y
    
record PartialOrder' {A} (_≈_ : Rel A) (_≤_ : Rel A) : Set where
  field
    preorder     : PreOrder _≤_
    antisymmetry : ∀ x y → x ≤ y → y ≤ x → x ≈ y
    
record TotalOrder {A} (_≈_ : Rel A) (_≤_ : Rel A) : Set where
  field
    po   : PartialOrder _≈_ _≤_ 
    univ : ∀ x y → (x ≤ y) ⊎ (y ≤ x)

record StrictOrder {A} (_<_ : Rel A) : Set where
  field
    irreflexivity : ∀ x → ¬ (x < x)
    transitivity  : ∀ x y z → x < y → y < z → x < z
    antisymmetry  : ∀ x y → x < y → ¬ (y < x) 
    
