-- Атомизм Демокрита.  Атомы имеют "интерфейс", позволяющий им соединяться
-- друг с другом.  Между ними пустота, иначе они сливаются.  Это похоже на
-- алфавит вместе с правилами сочетания букв.
-- Нужно определить конструкторы для тел.

open import TTCore

module Atomism where

data Atom : Set where
  α β γ δ : Atom

-- Правила комбинации атомов.
Rule : Atom → Atom → Set
Rule α β = ⊤
Rule β γ = ⊤
Rule γ δ = ⊤
Rule _ _ = ⊥

-- декларируем без определения
data Body : Set
left  : Body → Atom
right : Body → Atom

-- Теперь определяем.

-- Правила конструирования тел.
data Body where
  ⟨_⟩ : Atom → Body
  _◀_ : (a : Atom) → (b : Body) → {_ : Rule a (left b)} → Body   -- добавление слева
  _▶_ : (b : Body) → (a : Atom) → {_ : Rule (right b) a} → Body  -- добавление справа

-- Левый атом
left ⟨ a ⟩ = a
left (a ◀ _) = a
left (b ▶ _) = left b

-- Правый атом
right ⟨ a ⟩ = a
right (_ ◀ b) = right b
right (_ ▶ a) = a

-- Примеры

b1 : Body
b1 = α ◀ ⟨ β ⟩

b2 : Body
b2 = b1 ▶ γ

bα = ⟨ α ⟩
bβ = ⟨ β ⟩
bγ = ⟨ γ ⟩

b1' : Body
b1' = α ◀ bβ 

b2' : Body
b2' = b1' ▶ γ

_ : b1 ≡ b1'
_ = refl


-- impossible body
_ : Body
_ = α ◀ ⟨ γ ⟩
