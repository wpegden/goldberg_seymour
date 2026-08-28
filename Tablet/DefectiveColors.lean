import Tablet.DefectiveColor

-- [TABLET NODE: DefectiveColors]
noncomputable def DefectiveColors {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k)
    (X : Finset V) : Finset (Fin k) := by
-- BODY
  classical
  exact Finset.univ.filter fun alpha => DefectiveColor G phi X alpha
