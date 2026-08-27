import Tablet.ColoredVertexSetClosed
import Tablet.TashkinovAugmentationSequence
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: TashkinovClosure]
def TashkinovClosure {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (phi : PartialEdgeColoring E k) (T T' : TreeSequence G e0) : Prop :=
-- BODY
  TashkinovAugmentationSequence phi T T' ∧
    ColoredVertexSetClosed G phi (TreeSequenceVertexSet T')
