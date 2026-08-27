import Tablet.TwoColorComponent
import Tablet.TwoColorIncidenceDegreeAtMostTwo

-- [TABLET NODE: TwoColorComponentSpanningPath]
theorem TwoColorComponentSpanningPath {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k)
    (alpha beta : Fin k) (hproper : IsProperEdgeColoring G phi)
    (z : Sum V E) :
    ∃ (u v : Sum V E)
      (p : (TwoColorIncidenceGraph G phi alpha beta).Walk u v),
      p.IsPath ∧ {x | x ∈ p.support} = TwoColorComponent G phi alpha beta z := by
-- BODY
  sorry
