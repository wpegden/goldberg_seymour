import Tablet.TwoColorComponent
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: TwoColorPathComponent]
def TwoColorPathComponent {V E : Type*} (G : LooplessMultigraph V E)
    {k : ℕ} (phi : PartialEdgeColoring E k) (alpha beta : Fin k)
    (z : Sum V E) : Prop :=
-- BODY
  alpha ≠ beta ∧
    (∃ f : E, Sum.inr f ∈ TwoColorComponent G phi alpha beta z) ∧
    ∃ x ∈ TwoColorComponent G phi alpha beta z,
      Set.Subsingleton ((TwoColorIncidenceGraph G phi alpha beta).neighborSet x)
