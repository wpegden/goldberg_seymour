import Tablet.ColoringExists

-- [TABLET NODE: ChromaticIndex]
noncomputable def ChromaticIndex {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) : ℕ := by
-- BODY
  classical
  exact Nat.find (ColoringExists G)
