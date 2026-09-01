import Tablet.TwoColorComponent
import Tablet.TwoColorPathComponent

-- [TABLET NODE: TwoColorNontrivialPathComponent]
def TwoColorNontrivialPathComponent {V E : Type*}
    (G : LooplessMultigraph V E) {k : ℕ}
    (phi : PartialEdgeColoring E k) (alpha beta : Fin k)
    (z : Sum V E) : Prop :=
-- BODY
  TwoColorPathComponent G phi alpha beta z ∧
    ∃ f : E, Sum.inr f ∈ TwoColorComponent G phi alpha beta z
