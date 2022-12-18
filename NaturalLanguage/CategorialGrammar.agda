module CategorialGrammar where

open import Data.List using (List; _++_; length; reverse; map; foldr; downFrom; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

infix 8 _╲_
infix 8 _╱_

data Type : Set where
  N : Type                 -- noun
  NP : Type                -- noun phrase
  S : Type                 -- sentence
  _╲_ : Type → Type → Type
  _╱_ : Type → Type → Type

infix 7 _∙_
infix 6 _⦂_

data Term : Set where
  `_  : String → Term
  _∙_ : Term → Term → Term

data Judgment : Set where
  []  : Judgment
  _⦂_ : Term → Type → Judgment


Context = List Judgment

infix  4  _∋_

_∋_ : Context → Judgment → Set
_∋_ l j = j ∈ l 





-- Выводимость Γ ⊢ A

infix  4  _⊢_

data _⊢_ : Context → Judgment → Set where

  ⊢` : ∀ {Γ A}
    → Γ ∋ A
      -------------
    → Γ ⊢ A

  ⊢Ctx+ : ∀ {Γ A B}
    → Γ ⊢ A
      -----------------
    → B ∷ Γ ⊢ A


  ⊢\ : ∀ {Γ X Y a b}
    → Γ ⊢ a ⦂ X
    → Γ ⊢ b ⦂ X ╲ Y
      -------------
    → Γ ⊢ a ∙ b ⦂ Y
    
  ⊢/ : ∀ {Γ X Y a b}
    → Γ ⊢ a ⦂ X
    → Γ ⊢ b ⦂ Y ╱ X
      -------------
    → Γ ⊢ b ∙ a ⦂ Y

John = ` "John"
run = ` "run"
runs = run 

Γ : Context
Γ = John ⦂ N ∷ run ⦂ N ╲ S ∷ []

_ : John ⦂ N ∈ Γ
_ = here refl

_ : Γ ⊢ John ⦂ N
_ = ⊢` (here refl)

_ : Γ ⊢ John ∙ runs ⦂ S
_ = ⊢\ (⊢` (here refl)) (⊢` (there (here refl)))



Adj = N ╱ N               -- adjective
Det = NP ╱ N              -- determiner
IV  = NP ╲ S              -- intransitive verb 
TV  = (NP ╲ S) ╱ NP       -- transitive verb


-- the bad boy made that mess

the = ` "the"
bad = ` "bad"
boy = ` "boy"
made = ` "made"
that = ` "that"
mess = ` "mess"

Δ : Context
Δ = the ⦂ Det
  ∷ bad ⦂ Adj
  ∷ boy ⦂ N
  ∷ made ⦂ TV
  ∷ that ⦂ Det
  ∷ mess ⦂ N
  ∷ []

_ : Δ ⊢ (the ∙ (bad ∙ boy)) ∙ (made ∙ (that ∙ mess)) ⦂ S
_ = ⊢\ {X = NP} (⊢/ {X = N} (⊢/ {X = N} (⊢` (there (there (here refl)))) (⊢` (there (here refl))))
    (⊢` (here refl))) (⊢/ {X = NP} (⊢/ {X = N} (⊢` (there (there (there (there (there (here refl)))))))
    ((⊢` (there (there (there (there (here refl)))))))) ((⊢` (there (there (there (here refl)))))))

