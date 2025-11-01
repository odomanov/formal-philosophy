{-#  OPTIONS --type-in-type #-}     -- позволяет построить парадокс

module _ where

open import TTCore

-- индексированный универсум 
data U : Set where
  S : (I : Set) → (I → U) → U  -- каждое S это I вместе с его отображением в U

∅ : U
∅ = S ⊥ ⊥-elim

All : U             -- U принадлежит себе
All = S U id

_∈_ : U → U → Set 
A ∈ S I f = Σ I (λ i → A ≡ f i)

U∈U : S U id ∈ S U id 
U∈U = S U id , refl

_∉_ : U → U → Set
A ∉ B = A ∈ B → ⊥

R : U
R = S (Σ U (λ x → x ∉ x)) proj₁

-- сначала докажем леммы
lem-1 : ∀ {X} → X ∈ R → X ∉ X
lem-1 ((Y , Y∉Y) , refl) = Y∉Y

lem-2 : ∀ {X} →  X ∉ X → X ∈ R
lem-2 {X} X∉X = (X , X∉X) , refl

lem-3 : R ∉ R
lem-3 R∈R = lem-1 R∈R R∈R


-- contradiction
contr : ⊥
contr = lem-3 (lem-2 lem-3)


