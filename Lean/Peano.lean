/-  Аксиомы Пеано
    -------------
    1. 0 ∈ ℕ
    2. x ∈ ℕ => s(x) ∈ ℕ
    3. s(x) = s(y) <=> x = y
    4. ∀ x ¬ s(x) = 0
    5. Индукция                            -/

namespace Peano

#print Nat
inductive Nat₁ where
| zero : Nat₁
| succ : Nat₁ → Nat₁
#print Nat₁

open Nat

-- Ax.1, Ax.2 выполняются по определению
#check zero
#check succ
example : Nat := zero
example (x : Nat) : Nat := succ x

-- Ax.3
theorem Ax3 : ∀ x y : Nat, succ x = succ y → x = y := λ x y p =>
  match x, y, p with
  | zero, zero, rfl => rfl
  | succ n, _, rfl => rfl
#print Ax3

theorem Ax3b : ∀ x y : Nat, succ x = succ y → x = y
  | _, _, rfl => rfl
#print Ax3b


-- Ax.4
theorem Ax4c : ∀ x : Nat, ¬ zero = succ x := by intro _ h; injection h
#print Ax4c

theorem Ax4a : ∀ x : Nat, ¬ succ x = zero := by
  intros x p
  cases p
#print Ax4a

theorem Ax4a' : ∀ x : Nat, ¬ succ x = zero := by simp
#print Ax4a'

theorem Ax4b : ∀ x : Nat, ¬ zero = succ x := nofun
#print Ax4b


-- Ax.5
theorem Ax5 : (P : Nat → Prop)
  → P zero
  → (∀ n : Nat, P n → P (succ n))
  → ∀ m : Nat, P m
  := λ P p0 pn m =>
    match P, p0, pn, m with
    | _, z, _, zero => z
    | P, z, f, succ m => f m (Ax5 P z f m)

#print Nat.rec
