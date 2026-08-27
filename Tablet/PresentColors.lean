import Tablet.Incident
import Tablet.PartialEdgeColoring

-- [TABLET NODE: PresentColors]
noncomputable def PresentColors {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) {k : ℕ} (φ : PartialEdgeColoring E k)
    (v : V) : Finset (Fin k) := by
-- BODY
  classical
  exact Finset.univ.filter fun c => ∃ e, Incident G v e ∧ φ e = some c
