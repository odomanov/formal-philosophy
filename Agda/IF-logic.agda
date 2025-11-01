-- Hintikka's IF-logic (independence friendly)
-- ???
-- теория типов это логика высшего порядка, поэтому неудивительно, что там
-- формализуются предложения Хинтикки.  Другое дело, что эта формализация
-- может быть проще или естественнее.

module _ where

open import TTCore

-- Some critics admire only themselves.


-- (1) some relative of each villager and some relative of each townsman hate
--     each other

postulate
  D : Set
  V : D → Set          -- is villager
  T : D → Set          -- is townsman
  Rel  : D → D → Set   -- are relatives
  Hate : D → D → Set   -- hate each other

Vs = Σ[ x ∈ D ] V x   -- villagers
Ts = Σ[ x ∈ D ] T x   -- townsmen

-- townsmen who are relatives of a villager
VR : Vs → Set
VR v = Σ[ x ∈ Ts ] Rel (proj₁ v) (proj₁ x)   
-- villagers who are relatives of a townsman
TR : Ts → Set
TR t = Σ[ x ∈ Vs ] Rel (proj₁ t) (proj₁ x)   


s' = ∀ (v : Vs) (t : Ts) → Σ[ vr ∈ VR v ] Σ[ tr ∈ TR t ] (Hate (proj₁ (proj₁ vr)) (proj₁ (proj₁ tr)))

s'' = ∀ (v : Vs) (t : Ts) → Σ[ tr ∈ TR t ] Σ[ vr ∈ VR v ] (Hate (proj₁ (proj₁ vr)) (proj₁ (proj₁ tr)))


-- Let's prove that s' and s'' are equivalent

prf→ : s' → s''
prf→ es' v t = tr' , vr' , ht'
  where
  p = es' v t
  vr' = proj₁ p
  tr' = proj₁ (proj₂ p)
  -- ht' : Hate (proj₁ (proj₁ vr')) (proj₁ (proj₁ tr'))
  ht' = proj₂ (proj₂ p)

prf← : s'' → s'
prf← es'' v t = vr'' , tr'' , ht''
  where
  p = es'' v t
  tr'' = proj₁ p
  vr'' = proj₁ (proj₂ p)
  -- ht'' : Hate (proj₁ (proj₁ vr'')) (proj₁ (proj₁ tr''))
  ht'' = proj₂ (proj₂ p)



-- (2) Some book by every author is referred to in some essay by every critic.

-- (3) Every writer likes a book of his almost as much as every critic
--     dislikes some book he has reviewed.
