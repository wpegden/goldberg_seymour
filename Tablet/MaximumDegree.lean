import Tablet.Degree

-- [TABLET NODE: MaximumDegree]
noncomputable def MaximumDegree {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) : ℕ := by
-- BODY
  classical
  exact (insert 0 (Finset.univ.image fun v => Degree G v)).max' (by simp)
