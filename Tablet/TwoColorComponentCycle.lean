import Tablet.TwoColorComponent
import Tablet.TwoColorCycle

-- [TABLET NODE: TwoColorComponentCycle]
def TwoColorComponentCycle {V E : Type*} (G : LooplessMultigraph V E)
    {k : ℕ} (phi : PartialEdgeColoring E k) (alpha beta : Fin k)
    (z : Sum V E) : Prop :=
-- BODY
  ∃ cycle : TwoColorCycle G phi alpha beta,
    ∀ x : Sum V E,
      x ∈ cycle.walk.support ↔
        x ∈ TwoColorComponent G phi alpha beta z
