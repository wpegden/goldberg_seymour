import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorPathComponent

-- [TABLET NODE: TreeInterchangeable]
def TreeInterchangeable {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
    (alpha beta : Fin k) : Prop :=
-- BODY
  ∀ z w : Sum V E,
    TwoColorPathComponent G phi alpha beta z →
    TwoColorPathComponent G phi alpha beta w →
    (∃ v ∈ TreeSequenceVertexSet T,
      Sum.inl v ∈ TwoColorComponent G phi alpha beta z) →
    (∃ v ∈ TreeSequenceVertexSet T,
      Sum.inl v ∈ TwoColorComponent G phi alpha beta w) →
    TwoColorComponent G phi alpha beta z =
      TwoColorComponent G phi alpha beta w
