import Tablet.BoundaryColorEdges
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: TreeColorSetClosed]
def TreeColorSetClosed {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) {k : ℕ} {e0 : E}
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : Finset (Fin k)) : Prop :=
-- BODY
  ∀ alpha ∈ C,
    BoundaryColorEdges G phi (TreeSequenceVertexSet T) alpha = ∅
