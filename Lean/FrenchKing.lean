-- The present king of France is bald.

axiom Time : Type
axiom t0 : Time           -- present
axiom FrenchPeople : Type
axiom is_king_at : FrenchPeople → Time → Prop
axiom noKing : ∀(p : FrenchPeople), ¬ is_king_at p t0    -- no present king
axiom is_bald : FrenchPeople → Prop

-- тип французских королей
def King : Time → Type := λ t => Σ' x : FrenchPeople, (is_king_at x t)
#check King

-- тип нынешних королей
def PresentKing := King t0
#check PresentKing

theorem lem1 {P : α → Prop} : (∀ (x : α), ¬ P x) → ¬ ∃ x, P x :=
  λ p ⟨fst, snd⟩ => p fst snd

-- theorem lem2 : ¬ ∃ x : PresentKing, True := lem1 noKing
theorem lem2 : PresentKing → False := λ ⟨x1,x2⟩ => noKing x1 x2

-- предложение Рассела
def S := ∀ (x : PresentKing), (is_bald x.fst)

-- тривиально истинно
theorem tm1 : S := λ x => False.elim (lem2 x)

-- Рассел формализует через квантор существования, поэтому у него
-- предложение ложно.
-- (у Рассела есть ещё условие, что король всего один; мы его опускаем)

def Sᵣ := ∃ x : PresentKing, is_bald x.fst

theorem lem3 : (P : α → Prop) → (α → False) → ¬ ∃ x, P x
  | _, n, ⟨fst,_⟩ => n fst

theorem tm2 : Sᵣ → False
| x => lem3 _ lem2 x
