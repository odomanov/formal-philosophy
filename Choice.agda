-- Аксиома выбора

open import TTCore

module Choice where

-- Формулировка аксиомы.
-- P.Martin-Lof, An intuitionistic type theory-Bibliopolis (1984), p.50.
AC : Set₁
AC = {A B : Set} {C : A → B → Set}  
   → (∀ (x : A) → Σ[ y ∈ B ] C x y)                  -- непустота множеств
   → Σ[ f ∈ (A → B) ] ∀ (x : A) → C x (f x)

-- Доказательство AC тривиально.
prf : AC
prf g = (λ z → proj₁ (g z)) , (λ z → proj₂ (g z)) 


-- Классическая формулировка не доказывается в интуиционизме из-за
-- двойного отрицания.

CAC : Set₁
CAC = {A B : Set} {C : A → B → Set}  
    → (∀ (x : A)  → ¬ ¬ (Σ[ y ∈ B ] C x y))          -- непустота множеств
    → ¬ ¬ (Σ[ f ∈ (A → B) ] ∀ (x : A) → C x (f x))

-- Если вы знаете, что тип непуст, то это не значит, что вы знаете хотя бы
-- один элемент этого типа.
