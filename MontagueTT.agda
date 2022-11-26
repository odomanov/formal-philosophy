-- Montague semantics in terms of TT.


open import TTCore

module _ where

-- Синтаксические категории.
-- ========================

-- Проверка согласования типов производится на уровне синтаксиса.
-- Это не обязательно должно быть так.  Например, при этой формализации исключаются
-- фразы типа "Зелёные идеи яростно спят", т.е. правильные синтаксически, но
-- неправильные семантически.

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
    some every no the : DET

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

  postulate selected : (A : Set) → A → Set    -- выбор элемента A в разных прагматических ситуациях
  
  -- the domain of 'the' should be a singleton?
  ⟦det_⟧ : DET → (cn : CN)→ (⟦cn cn ⟧ → Set) → Set       -- DET = (e → t) → ((e → t) → t) 
  ⟦det some ⟧  cn ⟦vp⟧ = Σ ⟦cn cn ⟧ ⟦vp⟧ 
  ⟦det every ⟧ cn ⟦vp⟧ = (x : ⟦cn cn ⟧) → ⟦vp⟧ x
  ⟦det no ⟧    cn ⟦vp⟧ = (x : ⟦cn cn ⟧) → ¬ ⟦vp⟧ x 
  ⟦det the ⟧   cn ⟦vp⟧ = Σ[ x ∈ is-selected ] ⟦vp⟧ (proj₁ x)
    where
    is-selected = Σ[ t ∈ ⟦cn cn ⟧ ] (selected ⟦cn cn ⟧ t)
  
  ⟦ap_⟧ : {cn : CN} → AP cn → (⟦cn cn ⟧ → Set)           -- AP = (e → t) 
  ⟦ap ap-a big ⟧ = *big
  
  ⟦s_⟧ : S → Set
  ⟦s s-nv np vp ⟧ = ⟦np np ⟧ ⟦vp vp ⟧


s1 = s-nv (np-pn Mary) (vp-vi runs)

_ : ⟦s s1 ⟧ ≡ *runs *Mary
_ = refl



-- s3 = s-nv (np-pn Polkan) (vp-vi runs)     -- это не работает! нужна коэрсия


-- some human runs
s4 = s-nv (np-det some Human) (vp-vi runs)

_ : ⟦s s4 ⟧ ≡ Σ *Human *runs
_ = refl


-- every human runs
s5 = s-nv (np-det every Human) (vp-vi runs)

_ : ⟦s s5 ⟧ ≡ ((x : *Human) → *runs x)
_ = refl



-- the human runs
s6 = s-nv (np-det the Human) (vp-vi runs)

_ : ⟦s s6 ⟧
_ = (*Mary , is-selected) , *Mary-runs
  where
  postulate
    is-selected : selected *Human *Mary 
    *Mary-runs : *runs *Mary



-- Прилагательные / свойства

big-dog : ⟦cn cn-ap (ap-a big) ⟧ 
big-dog = *Polkan , *polkan-is-big 
  where postulate *polkan-is-big : *big *Polkan



-- Относительные конструкции (CN that VP и пр.)

human-that-runs : CN
human-that-runs = rcn Human (vp-vi runs)

_ : ⟦cn human-that-runs ⟧
_ = *Mary , *Mary-runs
  where postulate *Mary-runs : *runs *Mary


a-human-that-runs : NP _ 
a-human-that-runs = np-det some human-that-runs


--s9 = s-nv a-human-that-runs (vp-vi runs)   -- не работает!  нужна коэрсия



-- Mary loves Alex

s11 = s-nv (np-pn Mary) (vp-vt love (np-pn Alex))

-- Mary loves some human

s12 = s-nv (np-pn Mary) (vp-vt love (np-det some Human))

-- Every human loves some human

s13 = s-nv (np-det every Human) (vp-vt love (np-det some Human))


