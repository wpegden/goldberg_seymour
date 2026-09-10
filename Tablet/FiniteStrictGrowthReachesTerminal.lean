import Tablet.Preamble

-- [TABLET NODE: FiniteStrictGrowthReachesTerminal]
theorem FiniteStrictGrowthReachesTerminal
    {V : Type*} [Fintype V] [DecidableEq V]
    (State Terminal : Finset V → Prop)
    (grow : ∀ X, State X → ¬ Terminal X →
      ∃ Y, State Y ∧ X < Y)
    {X0 : Finset V} (hX0 : State X0) :
    ∃ X, State X ∧ Terminal X := by
-- BODY
  suffices hgo : ∀ X, State X → ∃ Y, State Y ∧ Terminal Y by
    exact hgo X0 hX0
  intro X
  induction X using
      (measure (fun X : Finset V => Fintype.card V - X.card)).wf.induction with
  | h X ih =>
    intro hX
    by_cases hterminal : Terminal X
    · exact ⟨X, hX, hterminal⟩
    · obtain ⟨Y, hY, hXY⟩ := grow X hX hterminal
      apply ih Y
      · have hcard : X.card < Y.card := Finset.card_lt_card hXY
        have hYcard : Y.card ≤ Fintype.card V := Finset.card_le_univ Y
        have hXcard : X.card < Fintype.card V := lt_of_lt_of_le hcard hYcard
        exact Nat.sub_lt_sub_left hXcard hcard
      · exact hY
