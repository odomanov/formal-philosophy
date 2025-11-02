-- Кроссмировая предикация
set_option quotPrecheck false

-- класс возможных миров
class PossWorlds where
  World : Type                  -- тип (возможных) миров
  w₀    : World                 -- актуальный мир
  acc   : World → World → Prop  -- acc w₁ w₂ = "w₂ достижим из w₁"

namespace CrossWorld
variable [PossWorlds]   --строим для нктр. класса миров
open PossWorlds

-- acc_worlds w = миры, достижимые из w
def acc_worlds : World → Type := λ w => { x : World // acc w x }

-- Возможно в мире w
notation "◇ " w:arg P:arg => ∃ x : acc_worlds w, P x.val

-- Необходимо в мире w
notation "□ " w:arg P:arg => ∀ x : acc_worlds w, P x.val


-- Примеры
-- =======

----------------------------------------------
-- I could have been taller than I actually am.
-- Я мог бы быть выше, чем я есть.

namespace I1

  axiom I : Type                 -- возможный я
  axiom i_I : World → I          -- интенсионал I
  local notation "^I" => i_I
  axiom taller : I → I → Prop

  -- Интенсионал taller: Я в мире w1 выше меня в мире w2
  inductive i_taller : World → World → Prop where
    | i : ∀ {w1 w2}, taller (^I w1) (^I w2) → i_taller w1 w2
  local notation "^taller" => i_taller

  -- Предикат: Я в мире w выше меня в актуальном мире
  def taller0 : World → Prop := λ w => ^taller w w₀

  -- I could have been taller than I actually am.
  -- Я мог бы быть выше, чем я есть.
  def trm : Prop := ◇ w₀ taller0

  -- то же в явной форме:
  def trm2 : Prop := ∃ w : acc_worlds w₀, taller (i_I w.1) (i_I w₀)

end I1

-- Другой вариант

namespace I2

  axiom D  : World → Type                          -- домены для каждого мира
  axiom i_I : (w : World) → D w                    -- интенсионал "Я"
  local notation:arg "^I/" w:arg => i_I w
  axiom taller {w1 w2 : World} : D w1 → D w2 → Prop

  -- Я в мире w1 выше меня в мире w2
  inductive i_taller : World → World → Prop where
    | i : ∀ {w1 w2}, taller ^I/w1 ^I/w2 → i_taller w1 w2
  local notation "^taller" => i_taller

  -- Дальше всё аналогично

  -- Предикат: Я в мире w выше меня в актуальном мире
  def taller0 : World → Prop := λ w => ^taller w w₀

  -- I could have been taller than I actually am.
  -- Я мог бы быть выше, чем я есть.
  def trm : Prop := ◇ w₀ taller0

  -- то же в явной форме:
  def trm2 : Prop := ∃ w : acc_worlds w₀, taller ^I/w.1 ^I/w₀

end I2



-- Джон мог бы быть богаче

namespace I3
  axiom D : World → Type
  axiom i_J : (w : World) → D w                  -- Джон в мире w
  local notation:arg "^J/" w:arg => i_J w
  axiom richer {w1 w2} : D w1 → D w2 → Prop  -- чел в мире w1 богаче чела в мире w2

  -- Джон в мире w1 богаче Джона в мире w2
  inductive Jr : World → World → Prop where
    | i : ∀ {w1 w2}, richer ^J/w1 ^J/w2 → Jr w1 w2

  -- Джон в мире w богаче Джона в актуальном мире
  def Jr0 := λ w => Jr w w₀

  -- Джон мог бы быть богаче
  def p1 := ◇ w₀ Jr0
  def p2 := ∀ w : acc_worlds w₀, richer ^J/w.1 ^J/w₀

end I3


-- =======================================================
-- Everyone could have been smarter than they actually are.
-- Каждый мог бы быть умнее, чем есть.

-- УПРАЖНЕНИЕ


-- =========================================================
-- A polar bear could be bigger than a grizzly bear could be.
-- Полярные медведи могли бы быть больше, чем могли бы быть гризли.
-- (некий) полярный медведь мог бы быть больше, чем мог бы быть (некий) гризли.

-- УПРАЖНЕНИЕ



namespace I4

-- Джон богаче, чем когда-либо прежде
-- Джон был богаче, чем когда-либо прежде

axiom Time : Type                 -- моменты времени
axiom pre  : Time → Time → Prop   -- t1 предшествует t2
local notation x:arg " < " y:arg => pre x y
axiom t0   : Time                -- момент "сейчас"
axiom J    : Type                 -- Джон в разные моменты
axiom i_J   : Time → J
axiom is_richer_than : J → J → Prop
local notation x:arg " is-richer-than " y:arg => is_richer_than x y

-- предшествующие моменты
def before : Time → Type
| t => { x : Time // x < t }

-- Джон богаче, чем когда-либо прежде
def jr0 := ∀(t : before t0), (i_J t0) is-richer-than (i_J t.1)

-- Джон был богаче, чем когда-либо прежде
axiom tp    : Time        -- момент в прошлом
axiom tp_pre_t0 : tp < t0

def jr := ∀(t : before tp), (i_J tp) is-richer-than (i_J t.1)

end I4


-- Для справки.
-- ===========

-- Миры, в которых я мог бы оказаться, это НЕ миры, в которых я могу оказаться.

namespace I5

-- Миры, в которых я могу оказаться:
axiom wposs : World → World → Prop  -- "я могу оказаться в мире w2, если нахожусь в мире w1"
local notation w1:arg " ⇒ " w2:arg => wposs w1 w2

def source : World → Type
| w => { x : World // x ⇒ w }  -- миры, из которых я мог попасть в w

-- Миры, в которых я мог бы оказаться.
-- Т.е. миры, в которых я могу оказаться из какого-то мира из 'source w1'.
def wwposs : World → World → Type := λ w1 w2 =>
  let P : source w1 → Prop := λ x => x.1 ⇒ w2
  { w : source w1 // P w }

end I5

-- If I were you, I wouldn’t bet on that horse.
-- If you were me, I wouldn’t bet on that horse.
-- I would be bolder if I weren’t me.
-- If I were you and you were me, I would be a rock star and you wouldn’t.

namespace I6
  -- The rich could have all been poor
  -- = there is a w in which all rich in w₀ are poor
  axiom D  : Type
  axiom is_in : D → World → Prop
  local notation d:arg " is-in " w:arg => is_in d w

  -- домен мира w
  def Dw : World → Type
    | w => { x : D // x is-in w }

  axiom is_rich : ∀ {w}, Dw w → Prop
  local notation x:arg " is-rich" => is_rich x
  axiom is_poor : ∀ {w}, Dw w → Prop
  local notation x:arg " is-poor" => is_poor x

  -- the Type of actually rich
  def act_rich : Type := { x : Dw w₀ // x is-rich }

  -- the one who is actually rich
  def ea : act_rich → D := λ x => x.1.1

  -- any actually rich is poor in w (if he exists in it)
  def P : World → Prop
  | w => ∀ (ar : act_rich) (q : (ea ar) is-in w), ⟨ea ar, q⟩ is-poor

  def P' : World → Prop
  | w => ∀ (ar : act_rich), ∃ q : (ea ar) is-in w, ⟨ea ar, q⟩ is-poor

  def s1 := ◇ w₀ P

  -- in full wording:
  def s1f := ∃ x : (Σ' w : World, acc w₀ w),
    ∀ (ar : act_rich) (q : (ea ar) is-in x.1), ⟨ea ar, q⟩ is-poor

  def s1' := ◇ w₀ P'
  #print s1'

  -- in full wording:
  def s1f' := ∃ x : (Σ' w : World, acc w₀ w),
    ∀ (ar : act_rich), ∃ q : (ea ar) is-in x.1, ⟨ea ar, q⟩ is-poor

-- Necessarily, the rich could have all been poor.

  def s2  := □ w₀ (λ w => ◇ w P)
  def s2' := □ w₀ (λ w => ◇ w P')

-- There is a polar bear that could be bigger than any grizzly bear could
-- be if the grizzly bear were fatter than the polar bear really is.

-- Necessarily, the rich could have all been millionaires if they were poor
-- in reality.
