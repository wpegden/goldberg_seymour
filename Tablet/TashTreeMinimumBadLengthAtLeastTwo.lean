import Tablet.AdjacentEdges
import Tablet.ChromaticIndex
import Tablet.ColoredVertexSetElementary
import Tablet.HasKEdgeColoring
import Tablet.Incident
import Tablet.IsFullEdgeColoring
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.TashTreeBadPair
import Tablet.TashTreeMinimumBadPair
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: TashTreeMinimumBadLengthAtLeastTwo]
theorem TashTreeMinimumBadLengthAtLeastTwo {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T) :
    2 ≤ T.length := by
-- BODY
  sorry
