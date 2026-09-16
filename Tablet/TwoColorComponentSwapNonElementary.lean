import Tablet.ColoredVertexSetElementary
import Tablet.IsProperEdgeColoring
import Tablet.MissingColorIncidenceEndpoint
import Tablet.MissingColors
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: TwoColorComponentSwapNonElementary]
theorem TwoColorComponentSwapNonElementary {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k)
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (hproper : IsProperEdgeColoring G phi) (z : Sum V E)
    (X : Finset V) (u v : V) (huX : u ∈ X) (hvX : v ∈ X)
    (huv : u ≠ v)
    (huC : Sum.inl u ∈ TwoColorComponent G phi alpha beta z)
    (hvC : Sum.inl v ∈ TwoColorComponent G phi alpha beta z)
    (hua : alpha ∈ MissingColors G phi u)
    (hvb : beta ∈ MissingColors G phi v)
    (hnot : ¬ ColoredVertexSetElementary G phi X) :
    ¬ ColoredVertexSetElementary G
      (TwoColorComponentSwap G phi alpha beta z) X := by
-- BODY
  sorry
