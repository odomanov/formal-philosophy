-- Cross-World Predication

open import TTCore

module CrossWorld where

postulate
  World : Set
  _≈>_ : World → World → Set  -- w1 ≈> w2    "w2 достижим из w1"
  w0 : World                  -- актуальный мир

-- Достижимые миры.
acc : World → Set
acc w = Σ World P
  where
  P : World → Set
  P w1 = w ≈> w1

-- Возможно в мире w
◇ : World → (P : World → Set) → Set
◇ w P = Σ (acc w) P'
  where
  P' : (acc w) → Set
  P' x = P (proj₁ x)

-- Необходимо в мире w
□ : World → (P : World → Set) → Set
□ w P = ∀ (x : acc w) → P (proj₁ x)



-- ===========================================
-- I could have been taller than I actually am.
-- Я мог бы быть выше, чем я есть.

postulate
  I : Set           -- возможный я
  ^I : World → I    -- интенсионал I
  taller : I → I → Set

-- Я в мире w1 выше меня в мире w2
data ^taller : World → World → Set where
  i : ∀ {w1 w2} → taller (^I w1) (^I w2) → ^taller w1 w2

-- Предикат: Я в мире w выше меня в актуальном мире
taller0 = λ w → ^taller w w0

-- I could have been taller than I actually am.
-- Я мог бы быть выше, чем я есть.
trm = ◇ w0 taller0

-- то же в явной форме:
trm2 = ∀ (w : acc w0) → taller (^I (proj₁ w)) (^I w0)



-- =======================================================
-- Everyone could have been smarter than they actually are.
-- Каждый мог бы быть умнее, чем есть.

-- УПРАЖНЕНИЕ


-- =========================================================
-- A polar bear could be bigger than a grizzly bear could be.
-- Полярные медведи могли бы быть больше, чем могли бы быть гризли.

-- УПРАЖНЕНИЕ



-- Джон богаче, чем когда-либо прежде
-- Джон был богаче, чем когда-либо прежде

postulate
  Time : Set                 -- моменты времени
  _<_  : Time → Time → Set   -- t1 предшествует t2
  t0   : Time                -- момент "сейчас"
  J    : Set                 -- Джон в разные моменты
  ^J   : Time → J
  _is-richer-than_ : J → J → Set

-- предшествующие моменты
before : Time → Set
before t = Σ Time (λ x → x < t)




-- Джон богаче, чем когда-либо прежде
jr0 = ∀ (t : before t0) → (^J t0) is-richer-than (^J (proj₁ t)) 


-- Джон был богаче, чем когда-либо прежде
postulate
  tp    : Time        -- момент в прошлом
  tp<t0 : tp < t0
  
jr = ∀ (t : before tp) → (^J tp) is-richer-than (^J (proj₁ t)) 




-- Для справки.
-- ===========

-- Миры, в которых я мог бы оказаться, это НЕ миры, в которых я могу оказаться.


-- Миры, в которых я могу оказаться:
postulate
  _⇒_ : World → World → Set  -- "я могу оказаться в мире w2, если нахожусь в мире w1"


source : World → Set
source w = Σ World (λ x → x ⇒ w)  -- миры, из которых я мог попасть в w


-- Миры, в которых я мог бы оказаться.
-- Т.е. миры, в которых я могу оказаться из какого-то мира из 'source w1'.
_≈≈>_ : World → World → Set
w1 ≈≈> w2 = Σ (source w1) P
  where
  P : (source w1) → Set
  P x = (proj₁ x) ⇒ w2

