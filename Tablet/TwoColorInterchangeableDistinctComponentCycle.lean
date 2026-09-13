import Tablet.IsProperEdgeColoring
import Tablet.TreeInterchangeable
import Tablet.TwoColorComponentCycle
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorPathComponent

-- [TABLET NODE: TwoColorInterchangeableDistinctComponentCycle]
theorem TwoColorInterchangeableDistinctComponentCycle {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
    (alpha beta : Fin k) (hproper : IsProperEdgeColoring G phi)
    (z w : Sum V E)
    (hzPath : TwoColorPathComponent G phi alpha beta z)
    (hinterchangeable : TreeInterchangeable G T phi alpha beta)
    (hzMeets : ∃ v ∈ TreeSequenceVertexSet T,
      Sum.inl v ∈ TwoColorComponent G phi alpha beta z)
    (hwMeets : ∃ v ∈ TreeSequenceVertexSet T,
      Sum.inl v ∈ TwoColorComponent G phi alpha beta w)
    (hdistinct : TwoColorComponent G phi alpha beta z ≠
      TwoColorComponent G phi alpha beta w) :
    TwoColorComponentCycle G phi alpha beta w := by
-- BODY
  sorry
