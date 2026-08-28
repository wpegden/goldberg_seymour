import Tablet.TashkinovTree
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: FixedPairMaximalTashkinovTree]
def FixedPairMaximalTashkinovTree {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) {k : ℕ} (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) : Prop :=
-- BODY
  TashkinovTree G e0 phi T ∧
    ∀ S : TreeSequence G e0, TashkinovTree G e0 phi S →
      TreeSequenceVertexSet T ⊆ TreeSequenceVertexSet S →
      TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet T
