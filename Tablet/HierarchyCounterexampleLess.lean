import Tablet.HierarchyCounterexampleMeasure

-- [TABLET NODE: HierarchyCounterexampleLess]
def HierarchyCounterexampleLess (a b : ℕ × ℕ) : Prop :=
-- BODY
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)
