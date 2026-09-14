import Tablet.TashTreeSuffixPath

-- [TABLET NODE: TashTreePathIndex]
noncomputable def TashTreePathIndex {V E : Type*}
    (G : LooplessMultigraph V E) {e0 : E} (T : TreeSequence G e0) : ℕ := by
-- BODY
  classical
  exact Nat.find (show ∃ q, TashTreeSuffixPath G T q by
    refine ⟨T.length, T.positive, le_rfl, ?_⟩
    intro i hi
    exact (Nat.not_lt_of_ge hi i.isLt).elim)
