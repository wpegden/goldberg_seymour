import Tablet.AdjacentEdges
import Tablet.IsProperEdgeColoring
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: TwoColorIncidenceDegreeAtMostTwo]
theorem TwoColorIncidenceDegreeAtMostTwo {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k)
    (alpha beta : Fin k) (hproper : IsProperEdgeColoring G phi)
    (z : Sum V E) :
    @SimpleGraph.degree _ (TwoColorIncidenceGraph G phi alpha beta) z
      (Fintype.ofFinite _) ≤ 2 := by
-- BODY
  sorry
