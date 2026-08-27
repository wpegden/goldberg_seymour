import Tablet.AdjacentEdges
import Tablet.IsProperEdgeColoring
import Tablet.MissingColors
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorIncidenceDegreeAtMostTwo

-- [TABLET NODE: MissingColorIncidenceEndpoint]
theorem MissingColorIncidenceEndpoint {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k)
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (hproper : IsProperEdgeColoring G phi) (v : V)
    (hmissing : alpha ∈ MissingColors G phi v) :
    @SimpleGraph.degree _ (TwoColorIncidenceGraph G phi alpha beta) (Sum.inl v)
      (Fintype.ofFinite _) ≤ 1 := by
-- BODY
  sorry
