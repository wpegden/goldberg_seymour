import Tablet.IsProperEdgeColoring
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: TwoColorComponentSwapMissingBehavior]
theorem TwoColorComponentSwapMissingBehavior {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k)
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (hproper : IsProperEdgeColoring G phi) (z : Sum V E) :
    let C := TwoColorComponent G phi alpha beta z
    let phi' := TwoColorComponentSwap G phi alpha beta z
    (∀ v : V, Sum.inl v ∉ C →
      MissingColors G phi' v = MissingColors G phi v) ∧
      (∀ v : V, Sum.inl v ∈ C →
        alpha ∈ MissingColors G phi v → beta ∈ MissingColors G phi' v) ∧
      (∀ v : V, Sum.inl v ∈ C →
        beta ∈ MissingColors G phi v → alpha ∈ MissingColors G phi' v) ∧
      ∀ v : V, ∀ c : Fin k, c ≠ alpha → c ≠ beta →
        (c ∈ MissingColors G phi' v ↔ c ∈ MissingColors G phi v) := by
-- BODY
  sorry
