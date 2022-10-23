-- Montague semantics in terms of TT.
-- Разделим формально синтаксис и семантику.

open import TTCore

module _ where

-- Синтаксические категории.
-- ========================

mutual

  data CN : Set where
    Human Dog : CN
    cn-ap : ∀ {cn} → AP cn → CN
    rcn : (cn : CN) → VP cn → CN    -- CN that VP
    
  data VI : CN → Set where
    runs : VI Human

  -- порядок аргументов в VT прямой!  VT A B => A → B → Set
  data VT : CN → CN → Set where
    love : VT Human Human
    
  data PN : CN → Set where
    Alex Mary : PN Human
    Polkan : PN Dog
  
  data DET : Set where
    an every no the : DET

  data Adj : CN → Set where
    big : Adj Dog
    
  data VP (cn : CN) : Set where
    vp-vi : VI cn → VP cn
    vp-vt : ∀ {cn1} → VT cn1 cn → NP cn1 → VP cn
  
  data NP : (cn : CN) → Set where
    np-pn  : ∀ {cn} → PN cn → NP cn
    np-det : DET → (cn : CN) → NP cn
  
  data AP (cn : CN) : Set where
    ap-a : Adj cn → AP cn
    
  data S : Set where
    s-nv  : ∀ {cn} → NP cn → VP cn → S
    s-det : DET → (cn : CN) → VP cn → S


-- Семантика
-- =========

postulate
  *Human *Dog : Set
  *Alex *Mary : *Human
  *Polkan : *Dog
  *runs : *Human → Set
  *love : *Human → *Human → Set
  *big : *Dog → Set 

mutual

  ⟦cn_⟧ : CN → Set
  ⟦cn Human ⟧ = *Human
  ⟦cn Dog ⟧ = *Dog
  ⟦cn cn-ap (ap-a big) ⟧ = Σ *Dog *big
  ⟦cn rcn cn vp ⟧ = Σ ⟦cn cn ⟧ ⟦vp vp ⟧
  
  ⟦pn_⟧ : {cn : CN} → PN cn → ⟦cn cn ⟧
  ⟦pn Alex ⟧ = *Alex
  ⟦pn Mary ⟧ = *Mary
  ⟦pn Polkan ⟧ = *Polkan

  ⟦vt_⟧ : ∀ {cn cn1} → VT cn cn1 → ⟦cn cn ⟧ → ⟦cn cn1 ⟧ → Set
  ⟦vt love ⟧ = *love

  {-# TERMINATING #-}
  ⟦vp_⟧ : {cn : CN} → VP cn → ⟦cn cn ⟧ → Set
  ⟦vp vp-vi runs ⟧ = *runs
  ⟦vp_⟧ {cn} (vp-vt {cn1} vt np) x = ∀ {r : cn ≡ cn1} → ⟦np np ⟧ (subst r (⟦vt vt ⟧ (subst r x)))

  -- the domain of 'the' should be a singleton?
  ⟦det_⟧ : DET → (cn : CN)→ (⟦cn cn ⟧ → Set) → Set
  ⟦det an ⟧    cn vp = Σ ⟦cn cn ⟧ vp 
  ⟦det every ⟧ cn vp = (x : ⟦cn cn ⟧) → vp x
  ⟦det no ⟧    cn vp = (x : ⟦cn cn ⟧) → ¬ vp x 
  ⟦det the ⟧   cn vp = Σ[ x ∈ (Σ[ z ∈ C ] vp z) ] Σ[ y ∈ C ] (y ≡ proj₁ x)   -- ???
    where
    C = ⟦cn cn ⟧
  
  
  ⟦np_⟧ : {cn : CN} → NP cn → (⟦cn cn ⟧ → Set) → Set
  ⟦np np-pn pn ⟧ vp = vp ⟦pn pn ⟧
  ⟦np np-det d cn ⟧ vp = ⟦det d ⟧ cn vp
  
  ⟦vi_⟧ : {cn : CN} → VI cn → ⟦cn cn ⟧ → Set
  ⟦vi runs ⟧ = *runs
  
  ⟦ap_⟧ : {cn : CN} → AP cn → (⟦cn cn ⟧ → Set)
  ⟦ap ap-a big ⟧ = *big
  
  ⟦s_⟧ : S → Set
  ⟦s s-nv np vp ⟧ = ⟦np np ⟧ ⟦vp vp ⟧
  ⟦s s-det d cn vp ⟧ = ⟦det d ⟧ cn ⟦vp vp ⟧


_ : ⟦pn Mary ⟧ ≡ *Mary
_ = refl

_ : ⟦vi runs ⟧ ≡ *runs
_ = refl

s1 = s-nv (np-pn Mary) (vp-vi runs)

_ : ⟦s s1 ⟧ ≡ *runs *Mary
_ = refl



-- s3 = s-nv (np-pn Polkan) (vp-vi runs)     -- это не работает! нужна коэрсия


-- a human runs
s4 = s-det an Human (vp-vi runs)

_ : ⟦s s4 ⟧ ≡ Σ *Human *runs
_ = refl


-- every human runs
s5 = s-det every Human (vp-vi runs)

_ : ⟦s s5 ⟧ ≡ ((x : *Human) → *runs x)
_ = refl



-- the human runs
s6 = s-det the Human (vp-vi runs)

postulate
  *Mary-runs : *runs *Mary

_ : ⟦s s6 ⟧
_ = (*Mary , *Mary-runs) , *Mary , refl



-- Прилагательные / свойства

postulate
  *polkan-is-big : *big *Polkan

big-dog : ⟦cn cn-ap (ap-a big) ⟧ 
big-dog = *Polkan , *polkan-is-big 


-- Относительные конструкции (CN that VP и пр.)

human-that-runs : CN
human-that-runs = rcn Human (vp-vi runs)

_ : ⟦cn human-that-runs ⟧
_ = *Mary , *Mary-runs


a-human-that-runs : NP _ 
a-human-that-runs = np-det an human-that-runs


--s9 = s-nv a-human-that-runs (vp-vi runs)   -- не работает!  нужна коэрсия



-- Mary loves Alex

s11 = s-nv (np-pn Mary) (vp-vt love (np-pn Alex))
