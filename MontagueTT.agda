-- Montague semantics in terms of TT.


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
    -- s-det : DET → (cn : CN) → VP cn → S


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

  ⟦cn_⟧ : CN → Set                        -- CN ≠ e → t !  CN это тип.
  ⟦cn Human ⟧ = *Human
  ⟦cn Dog ⟧ = *Dog
  ⟦cn cn-ap (ap-a big) ⟧ = Σ *Dog *big
  ⟦cn rcn cn vp ⟧ = Σ ⟦cn cn ⟧ ⟦vp vp ⟧
  
  ⟦pn_⟧ : {cn : CN} → PN cn → ⟦cn cn ⟧
  ⟦pn Alex ⟧ = *Alex
  ⟦pn Mary ⟧ = *Mary
  ⟦pn Polkan ⟧ = *Polkan

  ⟦np_⟧ : {cn : CN} → NP cn → (⟦cn cn ⟧ → Set) → Set   -- NP = (e → t) → t     
  ⟦np np-pn pn ⟧ ⟦vp⟧ = ⟦vp⟧ ⟦pn pn ⟧
  ⟦np np-det d cn ⟧ ⟦vp⟧ = ⟦det d ⟧ cn ⟦vp⟧
  
  ⟦vi_⟧ : {cn : CN} → VI cn → ⟦cn cn ⟧ → Set           -- VI = e → t
  ⟦vi runs ⟧ = *runs
  
  ⟦vt_⟧ : ∀ {cn cn1} → VT cn cn1 → ⟦cn cn ⟧ → ⟦cn cn1 ⟧ → Set    -- VT = e → e → t
  ⟦vt love ⟧ = *love

  {-# TERMINATING #-}
  ⟦vp_⟧ : {cn : CN} → VP cn → ⟦cn cn ⟧ → Set             -- VP = e → t
  ⟦vp vp-vi runs ⟧ = *runs
  ⟦vp_⟧ {cn} (vp-vt {cn1} vt np) x = ∀ {r : cn ≡ cn1} → ⟦np np ⟧ (subst _ r (⟦vt vt ⟧ (subst _ r x)))

  -- the domain of 'the' should be a singleton?
  ⟦det_⟧ : DET → (cn : CN)→ (⟦cn cn ⟧ → Set) → Set       -- DET = (e → t) → ((e → t) → t) 
  ⟦det an ⟧    cn ⟦vp⟧ = Σ ⟦cn cn ⟧ ⟦vp⟧ 
  ⟦det every ⟧ cn ⟦vp⟧ = (x : ⟦cn cn ⟧) → ⟦vp⟧ x
  ⟦det no ⟧    cn ⟦vp⟧ = (x : ⟦cn cn ⟧) → ¬ ⟦vp⟧ x 
  ⟦det the ⟧   cn ⟦vp⟧ = Σ[ x ∈ (Σ[ z ∈ ⟦C⟧ ] ⟦vp⟧ z) ] Σ[ y ∈ ⟦C⟧ ] (y ≡ proj₁ x)   -- ???
    where
    ⟦C⟧ = ⟦cn cn ⟧
  
  ⟦ap_⟧ : {cn : CN} → AP cn → (⟦cn cn ⟧ → Set)           -- AP = (e → t) 
  ⟦ap ap-a big ⟧ = *big
  
  ⟦s_⟧ : S → Set
  ⟦s s-nv np vp ⟧ = ⟦np np ⟧ ⟦vp vp ⟧
  -- ⟦s s-det d cn vp ⟧ = ⟦det d ⟧ cn ⟦vp vp ⟧


s1 = s-nv (np-pn Mary) (vp-vi runs)

_ : ⟦s s1 ⟧ ≡ *runs *Mary
_ = refl



-- s3 = s-nv (np-pn Polkan) (vp-vi runs)     -- это не работает! нужна коэрсия


-- a human runs
s4 = s-nv (np-det an Human) (vp-vi runs)
-- s4 = s-det an Human (vp-vi runs)

_ : ⟦s s4 ⟧ ≡ Σ *Human *runs
_ = refl


-- every human runs
s5 = s-nv (np-det every Human) (vp-vi runs)
-- s5 = s-det every Human (vp-vi runs)

_ : ⟦s s5 ⟧ ≡ ((x : *Human) → *runs x)
_ = refl



-- the human runs
s6 = s-nv (np-det the Human) (vp-vi runs)
-- s6 = s-det the Human (vp-vi runs)

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

-- Mary loves some human

s12 = s-nv (np-pn Mary) (vp-vt love (np-det an Human))

-- Every human loves some human

s13 = s-nv (np-det every Human) (vp-vt love (np-det an Human))


