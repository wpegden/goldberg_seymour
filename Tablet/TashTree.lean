import Tablet.ColoredVertexSetElementary
import Tablet.KTriple
import Tablet.MissingColors
import Tablet.TashkinovTree
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: TashTree]
theorem TashTree {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (htriple : KTriple G k e0 phi) (hT : TashkinovTree G e0 phi T) :
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) := by
-- BODY
  sorry
