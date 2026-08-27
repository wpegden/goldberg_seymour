import Tablet.RestrictEdges
import Tablet.IsProperEdgeColoring

-- [TABLET NODE: ProperColoringRestricts]
theorem ProperColoringRestricts {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) (F : Finset E) {k : ℕ}
    (φ : PartialEdgeColoring E k) (hφ : IsProperEdgeColoring G φ) :
    IsProperEdgeColoring (RestrictEdges G F) (fun e => φ e.1) := by
-- BODY
  intro e f c hne hadj he hf
  apply hφ (e := e.1) (f := f.1) ?_
      (by simpa [AdjacentEdges, Incident, RestrictEdges] using hadj) he hf
  intro hef
  apply hne
  exact Subtype.ext hef
