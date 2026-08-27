import Tablet.AdjacentEdges
import Tablet.IsProperEdgeColoring
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: TwoColorComponentSwapProper]
theorem TwoColorComponentSwapProper {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k)
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (hproper : IsProperEdgeColoring G phi) (z : Sum V E) :
    IsProperEdgeColoring G (TwoColorComponentSwap G phi alpha beta z) := by
-- BODY
  sorry
