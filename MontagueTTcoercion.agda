-- Montague semantics in terms of TT.
-- With coercion.

open import TTCore
open import Coercion renaming (_<:_ to _⟦<:⟧_)

module _ where

-- Синтаксические категории.
-- ========================

mutual

  data CN : Set where
    Human Dog Animate Object : CN
    cn-ap : ∀ {cn} → AP cn → (cn1 : CN) → {{coe : cn1 <: cn}} → CN
    rcn   : (cn : CN) {cn1 : CN} → {{coe : cn <: cn1}} → VP cn1 → CN    -- CN that VP
    
  data _<:_ : CN → CN → Set where
    instance cha  : Human <: Animate
    instance cda  : Dog <: Animate
    instance cao  : Animate <: Object
    instance cho  : Human <: Object
    instance cdo  : Dog <: Object
    instance ccc  : ∀ {cn} → cn <: cn
    instance crcn : ∀ {cn cn1 coe vp} → rcn cn {cn1} {{coe}} vp <: cn
    instance c∘   : ∀ {cn cn1 cn2} → cn <: cn1 → cn1 <: cn2 → cn <: cn2

  data VI : CN → Set where
    runs : VI Animate

  -- порядок аргументов в VT прямой!  VT A B => A → B → Set
  data VT : CN → CN → Set where
    love : VT Animate Object
    
  data PN : CN → Set where
    Alex Mary : PN Human
    Polkan    : PN Dog
  
  data DET : Set where
    an every no the : DET

  data Adj : CN → Set where
    big small : Adj Object
    
  -- порядок аргументов в VT прямой!
  data VP (cn : CN) : Set where
    vp-vi : VI cn → VP cn
    vp-vt : ∀ {cn1 cn2} → VT cn1 cn → {{coe : cn2 <: cn1}} → NP cn2 → VP cn
  
  data NP : (cn : CN) → Set where
    np-pn  : ∀ {cn} → PN cn → NP cn
    np-det : DET → (cn : CN) → NP cn
  
  data AP (cn : CN) : Set where
    ap-a : Adj cn → AP cn
    
  data S : Set where
    s-nv  : ∀ {cn} → NP cn → ∀ {cn1} → {{coe : cn <: cn1}} → VP cn1 → S


-- Семантика
-- =========

postulate
  *Human *Dog *Animate *Object : Set
  *Alex *Mary : *Human
  *Polkan : *Dog
  *runs : *Animate → Set
  *love : *Animate → *Object → Set
  *big : *Object → Set
  *small : *Object → Set 

postulate
  fDA : *Dog → *Animate
  fHA : *Human → *Animate
  fAO : *Animate → *Object
  
instance
  Ac : ∀ {ℓ} {A : Set ℓ} → A ⟦<:⟧ A
  Ac = identityCoercion
  HAc : *Human ⟦<:⟧ *Animate
  HAc = coerce fHA
  DAc : *Dog ⟦<:⟧ *Animate
  DAc = coerce fDA
  AOc : *Animate ⟦<:⟧ *Object
  AOc = coerce fAO
  HOc : *Human ⟦<:⟧ *Object
  HOc = AOc ⟪∘⟫ HAc           --coerce (fAO ∘ fHA)
  DOc : *Dog ⟦<:⟧ *Object
  DOc = AOc ⟪∘⟫ DAc           --coerce (fAO ∘ fDA)
  
mutual

  ⟦cn_⟧ : CN → Set                        -- CN ≠ e → t !  CN это тип.
  ⟦cn Human ⟧ = *Human
  ⟦cn Dog ⟧ = *Dog
  ⟦cn Animate ⟧ = *Animate
  ⟦cn Object ⟧ = *Object
  ⟦cn cn-ap ap cn {{coe}} ⟧ = ⟪Σ⟫ ⟦cn cn ⟧ ⟦ap ap ⟧ {{⟦coe coe ⟧}}  
  ⟦cn rcn cn {{coe = coe}} vp ⟧ = ⟪Σ⟫ ⟦cn cn ⟧ ⟦vp vp ⟧ {{⟦coe coe ⟧}} 

  ⟦coe_⟧ : {cn cn1 : CN} → (cn <: cn1) → (⟦cn cn ⟧ ⟦<:⟧ ⟦cn cn1 ⟧)
  ⟦coe cha ⟧ = HAc
  ⟦coe cda ⟧ = DAc
  ⟦coe cao ⟧ = AOc
  ⟦coe cho ⟧ = HOc    
  ⟦coe cdo ⟧ = DOc
  ⟦coe ccc ⟧ = Ac
  ⟦coe crcn ⟧ = refinementCoercion 
  ⟦coe c∘ c12 c23 ⟧ = ⟦coe c23 ⟧ ⟪∘⟫ ⟦coe c12 ⟧  

  ⟦pn_⟧ : {cn : CN} → PN cn → ⟦cn cn ⟧
  ⟦pn Alex ⟧   = *Alex 
  ⟦pn Mary ⟧   = *Mary 
  ⟦pn Polkan ⟧ = *Polkan 
  
  ⟦np_⟧ : {cn cn1 : CN} → NP cn →
        {{cc : ⟦cn cn ⟧ ⟦<:⟧ ⟦cn cn1 ⟧}} → (⟦cn cn1 ⟧ → Set) → Set  -- NP = (e → t) → t
  ⟦np np-pn pn ⟧    ⟦vp⟧ = ⟦vp⟧ ⟪ ⟦pn pn ⟧ ⟫
  ⟦np np-det d cn ⟧ ⟦vp⟧ = ⟦det d ⟧ cn ⟦vp⟧
  
  ⟦vi_⟧ : {cn : CN} → VI cn → ⟦cn cn ⟧ → Set           -- VI = e → t
  ⟦vi runs ⟧ = *runs

  ⟦vt_⟧ : ∀ {cn cn1} → VT cn cn1 → ⟦cn cn ⟧ → ⟦cn cn1 ⟧ → Set     -- VT = e → e → t
  ⟦vt love ⟧ = *love

  {-# TERMINATING #-}
  ⟦vp_⟧ : {cn0 cn01 : CN} → VP cn0 → {{cc : ⟦cn cn01 ⟧ ⟦<:⟧ ⟦cn cn0 ⟧}}
        → ⟦cn cn01 ⟧ → Set   -- VP = e → t
  -- ⟦vp copula ⟧ = {!!}
  ⟦vp vp-vi vi ⟧ x = ⟦vi vi ⟧ ⟪ x ⟫
  ⟦vp_⟧ {cn01 = cn01} (vp-vt {cn2 = cn2} vt {{coe}} np) {{cc}} x =
      ∀ {r : cn01 ≡ cn2} → ⟦np np ⟧ {{subst _ r cc}}
                           (⟦vt vt ⟧ (⟪ x ⟫ {{⟦coe (subst _ (symmetry r) coe) ⟧}}))
    where
    symmetry : ∀ {x y} → x ≡ y → y ≡ x
    symmetry refl = refl

  -- DET = (e → t) → ((e → t) → t) 
  -- the domain of 'the' should be a singleton?
  ⟦det_⟧ : DET → (cn : CN) → {cn1 : CN} → {{_ : ⟦cn cn ⟧ ⟦<:⟧ ⟦cn cn1 ⟧}}
         → (⟦cn cn1 ⟧ → Set) → Set 
  ⟦det an ⟧    cn ⟦vp⟧ = Σ ⟦cn cn ⟧ ⟪→ ⟦vp⟧ ⟫ 
  ⟦det every ⟧ cn ⟦vp⟧ = (x : ⟦cn cn ⟧) → ⟦vp⟧ ⟪ x ⟫
  ⟦det no ⟧    cn ⟦vp⟧ = (x : ⟦cn cn ⟧) → ¬ ⟦vp⟧ ⟪ x ⟫ 
  ⟦det the ⟧   cn ⟦vp⟧ = Σ[ x ∈ (Σ[ z ∈ ⟦C⟧ ] ⟦vp⟧ ⟪ z ⟫) ] Σ[ y ∈ ⟦C⟧ ] (y ≡ proj₁ x)   -- ???
    where
    ⟦C⟧ = ⟦cn cn ⟧
  
  ⟦ap_⟧ : {cn : CN} → AP cn → (⟦cn cn ⟧ → Set)        -- AP = (e → t) 
  ⟦ap ap-a big ⟧ = *big
  ⟦ap ap-a small ⟧ = *small
  
  ⟦s_⟧ : S → Set
  ⟦s s-nv np {{coe = coe}} vp ⟧ = ⟦np np ⟧ (⟪→ ⟦vp vp ⟧ ⟫ {{⟦coe coe ⟧}})



s1 = s-nv (np-pn Mary) (vp-vi runs)

_ : ⟦s s1 ⟧ ≡ *runs ⟪ *Mary ⟫
_ = refl



s3 = s-nv (np-pn Polkan) (vp-vi runs)     -- работает!


-- a human runs
s4 = s-nv (np-det an Human) (vp-vi runs)

_ : ⟦s s4 ⟧ ≡ ⟪Σ⟫ *Human *runs 
_ = refl


-- every human runs
s5 = s-nv (np-det every Human) (vp-vi runs)

_ : ⟦s s5 ⟧ ≡ ((x : *Human) → *runs ⟪ x ⟫)
_ = refl



-- the human runs
s6 = s-nv (np-det the Human) (vp-vi runs)

postulate
  *Mary-runs : *runs ⟪ *Mary ⟫

_ : ⟦s s6 ⟧
_ = (*Mary , *Mary-runs) , *Mary , refl



-- Прилагательные / свойства

postulate
  *polkan-is-big : *big ⟪ *Polkan ⟫

big-dog : ⟦cn cn-ap (ap-a big) Dog ⟧ 
big-dog = *Polkan , *polkan-is-big 


-- Относительные конструкции (CN that VP и пр.)

human-that-runs : CN
human-that-runs = rcn Human (vp-vi runs)

_ : ⟦cn human-that-runs ⟧
_ = *Mary , *Mary-runs


a-human-that-runs : NP _ 
a-human-that-runs = np-det an human-that-runs


-- a human that runs runs
s9 = s-nv a-human-that-runs {{c∘ crcn cha}} (vp-vi runs)   -- работает! 



-- Mary loves Alex

loves-Alex : VP _
loves-Alex = vp-vt love (np-pn Alex)

s11 = s-nv (np-pn Mary) loves-Alex

-- Mary loves Polkan

s12 = s-nv (np-pn Mary) (vp-vt love (np-pn Polkan))

-- Mary loves a human that runs

s13 = s-nv (np-pn Mary) (vp-vt love {{c∘ crcn cha}} a-human-that-runs)
