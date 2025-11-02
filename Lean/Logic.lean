-- Логика

namespace Logic

----------------------------------
--== пропозициональная логика ==--

-- встроено
theorem proof_irrel {P : Prop} (p q : P) : p = q := rfl

-- импликация это просто функция:
example : ∀ {P Q : Prop}, P → Q → P := λ p => λ _ => p

-- modus ponens
theorem mp : ∀ {P Q : Prop}, (P → Q) → P → Q := id

example {P Q : Prop} : P → (P → Q) → Q := λ p pq => mp pq p
example {P Q : Prop} : P → (P → Q) → Q := λ p pq => pq p

-- истина и ложь --

#print True
inductive True₁ : Prop where
  | intro : True₁                -- чаще trivial

#print trivial
theorem trivial : True := ⟨⟩

example : True := .intro
example : True := trivial

#print False
inductive False₁ : Prop where

-- конъюнкция --

#print And
structure And₁ (P Q : Prop) : Prop where
  intro ::
  left  : P
  right : Q

#check True ∧ True
example : (True ∧ True) = (And True True) := rfl
example : True ∧ True := ⟨ .intro, .intro ⟩
example : True ∧ True := ⟨ trivial, trivial ⟩

#check And.elim

example {P Q : Prop} : P ∧ Q → Q ∧ P := λ h => ⟨And.right h, And.left h⟩
example {P Q : Prop} : P ∧ Q → Q ∧ P := λ h => ⟨h.right, h.left⟩
example {P Q : Prop} : P ∧ Q → Q ∧ P := λ h => ⟨h.2, h.1⟩
example {P Q : Prop} : P ∧ Q → Q ∧ P := λ ⟨l,r⟩ => ⟨r,l⟩
example {P Q : Prop} : P ∧ Q → Q ∧ P
  | h => ⟨h.right,h.left⟩
example {P Q : Prop} : P ∧ Q → Q ∧ P
  | ⟨l,r⟩ => ⟨r,l⟩
example {P Q : Prop} : P ∧ Q → Q ∧ P := λ h =>
  have hp : P := h.left
  have hq : Q := h.right
  ⟨hq,hp⟩
example {P Q : Prop} : P ∧ Q → Q ∧ P := λ h =>
  have hp : P := h.left
  suffices hq : Q from ⟨hq,hp⟩
  h.right


-- отрицание --

#print Not
def Not₁ (P : Prop) : Prop := P → False

example : ¬ False := fun x => x

#check Not.elim
#check absurd


example {P Q R : Prop} : ¬P → Q → (Q → P) → R := sorry

-- modus tolens
theorem mt : ∀ {P Q : Prop}, (P → Q) → ¬ Q → ¬ P := sorry

theorem not_not_intro {P : Prop} : P → ¬ ¬ P := sorry


-- дизъюнкция --

#print Or
inductive Or₁ (a b : Prop) : Prop where
  | inl (h : a) : Or₁ a b
  | inr (h : b) : Or₁ a b

#check Or.elim

example : True ∨ False := .inl .intro
example : True ∨ False := .inl trivial

example {P Q : Prop} (h : P ∨ Q) : Q ∨ P :=
  Or.elim h
    (fun hp : P => Or.inr hp)
    (fun hq : Q => Or.inl hq)


-- iff --

#print Iff
structure Iff₁ (P Q : Prop) : Prop where
  intro ::
  mp  : P → Q
  mpr : Q → P

theorem and_swap {P Q : Prop} : P ∧ Q ↔ Q ∧ P :=
  Iff.intro
    (fun h : P ∧ Q => And.intro (And.right h) (And.left h))   -- P ∧ Q → Q ∧ P
    (fun h : Q ∧ P => And.intro (And.right h) (And.left h))   -- Q ∧ P → P ∧ Q

-- другие варианты записи:

theorem and_swap' {P Q : Prop} : P ∧ Q ↔ Q ∧ P :=
  Iff.intro
    (fun h => ⟨ h.right, h.left ⟩ )   -- P ∧ Q → Q ∧ P
    (fun h => ⟨ h.right, h.left ⟩ )   -- Q ∧ P → P ∧ Q

theorem and_swap'' {P Q : Prop} : P ∧ Q ↔ Q ∧ P :=
  ⟨ fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩ ⟩

theorem and_swap''' {P Q : Prop} : P ∧ Q ↔ Q ∧ P :=
  ⟨ fun ⟨l,r⟩ => ⟨r,l⟩, fun ⟨l,r⟩ => ⟨r,l⟩ ⟩

theorem and_swap'''' {P Q : Prop} : P ∧ Q ↔ Q ∧ P :=
  ⟨ f, f ⟩
  where
  f {X Y : Prop} : X ∧ Y → Y ∧ X := fun h => ⟨h.right, h.left⟩


example {P Q : Prop} : (P ↔ Q) → Q → P := λ h hq => h.mpr hq



-------------------------------------
--== Пропозициональное равенство ==--

#print Eq
inductive Eq₁ : α → α → Prop where
  | refl (a : α) : Eq₁ a a

#print rfl
def rfl₁ {α : Sort u} {a : α} : Eq a a := Eq.refl a

example : 2 + 3 = 5 := rfl

def f1 : Nat → Nat := λ n => n + 2
def f2 : Nat → Nat := (. + 2)
example : f2 = f1 := rfl

-- Подстановка (в HoTT называется transport)
#check Eq.subst

example (a b : α) (P : α → Prop) (h1 : a = b) (h2 : P a) : P b := h1 ▸ h2

theorem ne_false_of_self {P : Prop} : P → P ≠ False :=
  λ p pf => pf ▸ p

theorem true_ne_false : True ≠ False := sorry

-- равенство это эквивалентность:
theorem refl : ∀ {a : α}, a = a := rfl
theorem symm : ∀ {a b : α}, a = b → b = a := λ x => x ▸ rfl
theorem trans : ∀ {a b c : α}, a = b → b = c → a = c := λ ab bc => bc ▸ ab ▸ rfl

#check Eq.refl
#check Eq.symm
#check Eq.trans

#check congrArg
#check congrFun
#check congr

-- док-во congrArg
example {a₁ a₂ : α} (f : α → β) (h : a₁ = a₂) : f a₁ = f a₂ := h ▸ rfl



----------------------------
--== логика предикатов  ==--

example {P Q : α → Prop} : (∀ x, P x ∧ Q x) → ∀ y, P y :=
  λ h : (∀ x, P x ∧ Q x) => λ y : α => (h y).left

theorem eq_trans : ∀ {a b c : α}, a = b → b = c → a = c :=
  λ ab bc => bc ▸ ab ▸ rfl

#print Exists
inductive Exists₁ {α : Sort u} (P : α → Prop) : Prop where
  | intro (w : α) (h : P w) : Exists₁ P

example : ∃ x, x + 1 = 2 := ⟨1,rfl⟩

#check Exists.elim

example {P Q : α → Prop} (h : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x :=
  Exists.elim h
    (λ a (pa : P a ∧ Q a) => ⟨a, pa.right, pa.left⟩)

example {P Q : α → Prop} (h : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x :=
  let ⟨x, px, qx⟩ := h
  -- have ⟨x, px, qx⟩ := h
  ⟨x, qx, px⟩

example {P Q : α → Prop} : (h : ∃ x, P x ∧ Q x) → ∃ x, Q x ∧ P x
  | ⟨x, px, qx⟩ => ⟨x, qx, px⟩

example {P Q : α → Prop} : (h : ∃ x, P x ∧ Q x) → ∃ x, Q x ∧ P x :=
  fun ⟨x, px, qx⟩ => ⟨x, qx, px⟩

example {P Q : α → Prop} (h : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x :=
  ⟨h.choose, h.choose_spec.right, h.choose_spec.left⟩

example {P : α → Prop} {Q : Prop} : (∀ x, P x → Q) → (∃ x, P x) → Q :=
  λ f ep => let ⟨a,pa⟩ := ep; f a pa


-- парадокс брадобрея

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have ⟨bx, xx⟩ := h barber
  let sbb := shaves barber barber
  have np : sbb → False := λ x => (bx x) (xx (bx x))
  have p : sbb := xx np
  np p
