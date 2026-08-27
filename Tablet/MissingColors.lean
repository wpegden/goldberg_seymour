import Tablet.PresentColors

-- [TABLET NODE: MissingColors]
noncomputable def MissingColors {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) {k : ℕ} (φ : PartialEdgeColoring E k)
    (v : V) : Finset (Fin k) := by
-- BODY
  classical
  exact Finset.univ \ PresentColors G φ v
