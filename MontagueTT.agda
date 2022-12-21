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

  -- CN ни от чего не зависит
  data CN : Set where
    Human Dog : CN
    cn-ap : ∀ {cn} → AP cn → CN        -- пример: big Dog
    rcn : (cn : CN) → VP cn → CN       -- CN that VP

  -- VI зависит от CN
  data VI : CN → Set where
    runs : VI Human              -- runs применимо к Human

  data VT : CN → CN → Set where
    love : VT Human Human

  -- PN зависит от CN
  data PN : CN → Set where
    Alex Mary : PN Human         -- Alex, Mary относятся к Human
    Polkan : PN Dog              -- Polkan относится к Dog
  
  data DET : Set where
    some every no the : DET

  data Adj : CN → Set where
    big : Adj Dog

  -- VP зависит от CN (к чему применима глагольная группа VP)
  data VP (cn : CN) : Set where
    vp-vi  : VI cn → VP cn
    vp-vt1 : ∀ {cn2} → VT cn cn2 → NP cn2 → VP cn
    vp-vt2 : ∀ {cn1} → VT cn1 cn → NP cn1 → VP cn    -- для пассива

  -- NP зависит от CN (к какому CN относится NP)
  data NP : (cn : CN) → Set where
    np-pn  : ∀ {cn} → PN cn → NP cn
    np-det : DET → (cn : CN) → NP cn
  
  data AP (cn : CN) : Set where
    ap-a  : Adj cn → AP cn
    ap-ap : Adj cn → AP cn → AP cn

  
  -- в предложении NP и VP должны зависеть от одного и того же CN
  data S : Set where
    s-nvp : ∀ {cn} → NP cn → VP cn → S
    s-nvn : ∀ {cn1 cn2} → NP cn1 → VT cn1 cn2 → NP cn2 → S


-- Семантика
-- =========

-- Звёздочкой в начале обозначаем то, что относится к онтологии -- объекты,
-- функции на них и пр.

postulate
  *Human *Dog : Set
  *Alex *Mary : *Human
  *Polkan     : *Dog
  _*runs      : *Human → Set
  _*love_     : *Human → *Human → Set
  *big        : *Dog → Set 

-- тип A с выделенным элементом  -- нужен для определения 'the'
record Pointed (A : Set) : Set where
  field
    theₚ : A
open Pointed    


-- Определяем функции интерпретации для всех синтаксических категорий.

mutual

  ⟦cn_⟧ : CN → Set                        -- CN ≠ e → t !  CN это тип.
  ⟦cn Human ⟧ = *Human
  ⟦cn Dog ⟧ = *Dog
  ⟦cn cn-ap (ap-a big) ⟧ = Σ *Dog *big
  ⟦cn cn-ap {cn} ap ⟧ = Σ ⟦cn cn ⟧ ⟦ap ap ⟧   
  ⟦cn rcn cn vp ⟧ = Σ ⟦cn cn ⟧ ⟦vp vp ⟧
  
  ⟦pn_⟧ : {cn : CN} → PN cn → ⟦cn cn ⟧
  ⟦pn Alex ⟧ = *Alex
  ⟦pn Mary ⟧ = *Mary
  ⟦pn Polkan ⟧ = *Polkan

  ⟦np_⟧ : {cn : CN} → NP cn → (⟦cn cn ⟧ → Set) → Set   -- NP = (e → t) → t     
  ⟦np np-pn pn ⟧ ⟦vp⟧ = ⟦vp⟧ ⟦pn pn ⟧
  ⟦np np-det d cn ⟧ ⟦vp⟧ = ⟦det d ⟧ cn ⟦vp⟧
  
  ⟦vi_⟧ : {cn : CN} → VI cn → ⟦cn cn ⟧ → Set           -- VI = e → t
  ⟦vi runs ⟧ = _*runs
  
  ⟦vt_⟧ : ∀ {cn cn1} → VT cn cn1 → ⟦cn cn ⟧ → ⟦cn cn1 ⟧ → Set    -- VT = e → e → t
  ⟦vt love ⟧ = _*love_

  ⟦vp_⟧ : {cn : CN} → VP cn → ⟦cn cn ⟧ → Set             -- VP = e → t
  ⟦vp vp-vi runs ⟧ = _*runs
  ⟦vp vp-vt1 vt np ⟧ x = ⟦np np ⟧ λ y → ⟦vt vt ⟧ x y              -- λx.(NP (λy.(VT x y)))
  ⟦vp vp-vt2 vt np ⟧ x = ⟦np np ⟧ λ y → ⟦vt vt ⟧ y x              -- λx.(NP (λy.(VT y x)))

  ⟦det_⟧ : DET → (cn : CN)→ (⟦cn cn ⟧ → Set) → Set       -- DET = (e → t) → ((e → t) → t) 
  ⟦det some ⟧  cn ⟦vp⟧ = Σ ⟦cn cn ⟧ ⟦vp⟧ 
  ⟦det every ⟧ cn ⟦vp⟧ = (x : ⟦cn cn ⟧) → ⟦vp⟧ x
  ⟦det no ⟧    cn ⟦vp⟧ = (x : ⟦cn cn ⟧) → ¬ ⟦vp⟧ x 
  ⟦det the ⟧   cn ⟦vp⟧ = Σ[ Aₚ ∈ Pointed ⟦cn cn ⟧ ] ⟦vp⟧ (theₚ Aₚ)
  
  {-# TERMINATING #-}
  ⟦ap_⟧ : {cn : CN} → AP cn → (⟦cn cn ⟧ → Set)           -- AP = (e → t) 
  ⟦ap ap-a big ⟧ = *big
  ⟦ap_⟧ {cn} (ap-ap adj ap) x = Σ[ y ∈ Σ ⟦cn cn ⟧ ⟦ap ap-a adj ⟧ ] ⟦ap ap ⟧ (proj₁ y)

  -- Возможны множественные интерпретации.
  ⟦s_⟧ : S → List Set
  ⟦s s-nvp np vp ⟧ = ⟦np np ⟧ ⟦vp vp ⟧ ∷ []
  ⟦s s-nvn np1 vt np2 ⟧ = ⟦np np1 ⟧ (λ x → (⟦np np2 ⟧ λ y → ⟦vt vt ⟧ x y))   -- = ⟦np np1 ⟧ ⟦vp vp-vt1 vt np2 ⟧
                        ∷ ⟦np np2 ⟧ (λ x → (⟦np np1 ⟧ λ y → ⟦vt vt ⟧ y x))
                        ∷ []

-- проверим равенство
_ : ∀ {cn1 cn2}{np1 : NP cn1}{np2 : NP cn2}{vt : VT cn1 cn2}
    → ⟦np np1 ⟧ (λ x → (⟦np np2 ⟧ λ y → ⟦vt vt ⟧ x y)) ≡ ⟦np np1 ⟧ ⟦vp vp-vt1 vt np2 ⟧
_ = refl



-- Примеры
-- -------

s1 = s-nvp (np-pn Mary) (vp-vi runs)

_ : ⟦s s1 ⟧ ≡ *Mary *runs ∷ [] 
_ = refl



-- s3 = s-nvp (np-pn Polkan) (vp-vi runs)     -- это не работает! нужна коэрсия


-- some human runs
s4 = s-nvp (np-det some Human) (vp-vi runs)

_ : ⟦s s4 ⟧ ≡ Σ *Human _*runs ∷ []
_ = refl


-- every human runs
s5 = s-nvp (np-det every Human) (vp-vi runs)

_ : ⟦s s5 ⟧ ≡ ((x : *Human) → x *runs) ∷ []
_ = refl



-- the human runs
s6 = s-nvp (np-det the Human) (vp-vi runs)

_ : ⟦s s6 ⟧ ≡ (Σ[ Aₚ ∈ Pointed *Human ] (theₚ Aₚ) *runs) ∷ []
_ = refl


-- вспомогательные функции
inhabited : ∀ {a} {A : Set a} → List A → Set
inhabited [] = ⊥
inhabited _  = ⊤

head : ∀ {a}{A : Set a} → (l : List A) → {_ : inhabited l} → A
head (x ∷ _) = x   


_ : head ⟦s s6 ⟧
_ = Hₚ , *Mary-runs
  where
  Hₚ : Pointed *Human 
  Hₚ = record { theₚ = *Mary }

  postulate *Mary-runs : *Mary *runs



-- Прилагательные / свойства

big-dog : ⟦cn cn-ap (ap-a big) ⟧ 
big-dog = *Polkan , *polkan-is-big 
  where postulate *polkan-is-big : *big *Polkan



-- Относительные конструкции (CN that VP и пр.)

human-that-runs : CN
human-that-runs = rcn Human (vp-vi runs)

_ : ⟦cn human-that-runs ⟧
_ = *Mary , *Mary-runs
  where postulate *Mary-runs : *Mary *runs 


a-human-that-runs : NP _ 
a-human-that-runs = np-det some human-that-runs


--s9 = s-nvp a-human-that-runs (vp-vi runs)   -- не работает!  нужна коэрсия



-- Mary loves Alex

s11 = s-nvp (np-pn Mary) (vp-vt1 love (np-pn Alex))

_ : ⟦s s11 ⟧ ≡ *Mary *love *Alex ∷ []          
_ = refl


-- Mary loves some human

s12 = s-nvp (np-pn Mary) (vp-vt1 love (np-det some Human))

_ : ⟦s s12 ⟧ ≡ (Σ[ x ∈ *Human ] *Mary *love x) ∷ []
_ = refl


-- Every human loves some human (possibly different)   -- ср. s17

s13 = s-nvp (np-det every Human) (vp-vt1 love (np-det some Human))

_ : ⟦s s13 ⟧ ≡ (∀ (x : *Human) → Σ[ y ∈ *Human ] (x *love y)) ∷ []
_ = refl


-- Alex loves Mary / Mary is loved by Alex

s14 = s-nvp (np-pn Mary) (vp-vt2 love (np-pn Alex))

_ : ⟦s s14 ⟧ ≡ *Alex *love *Mary ∷ []          
_ = refl


-- Some human loves Mary / Mary is loved by some human

s15 = s-nvp (np-pn Mary) (vp-vt2 love (np-det some Human))

_ : ⟦s s15 ⟧ ≡ (Σ[ x ∈ *Human ] x *love *Mary) ∷ []
_ = refl


-- Every human is loved by some human (possibly different)

s16 = s-nvp (np-det every Human) (vp-vt2 love (np-det some Human))

_ : ⟦s s16 ⟧ ≡ (∀ (x : *Human) → Σ[ y ∈ *Human ] (y *love x)) ∷ []
_ = refl




-- Двусмысленное предложение:
-- Every human loves some human

s17 = s-nvn (np-det every Human) love (np-det some Human)

_ : ⟦s s17 ⟧ ≡ (∀ (x : *Human) → Σ[ y ∈ *Human ] (x *love y))  -- x love different humans
             ∷ (Σ[ y ∈ *Human ] (∀ (x : *Human) → x *love y))  -- x love the same human
             ∷ []
_ = refl


-- НО!
-- Два смысла предложения могут и совпадать:

s18 = s-nvn (np-pn Mary) love (np-pn Alex)

_ : ⟦s s18 ⟧ ≡ (*Mary *love *Alex)
             ∷ (*Mary *love *Alex)
             ∷ []
_ = refl            
