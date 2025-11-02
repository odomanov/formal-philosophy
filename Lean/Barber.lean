variable
  (men : Type)
  (barber : men)
  (shaves : men → men → Prop)

theorem B : (∀ x : men, shaves barber x ↔ ¬ shaves x x) → False := by
  intro h
  have p := h barber
  by_cases sbb : shaves barber barber
  · have nsbb : ¬ (shaves barber barber) := p.mp sbb
    contradiction
  · have nsbb : shaves barber barber := p.mpr sbb
    contradiction
