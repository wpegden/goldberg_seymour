import Tablet.AdjacentEdges
import Tablet.ChromaticIndex
import Tablet.ColoredVertexSetElementary
import Tablet.Degree
import Tablet.HasKEdgeColoring
import Tablet.Incident
import Tablet.IsFullEdgeColoring
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.MaximumDegree
import Tablet.MissingColorIncidenceEndpoint
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.TashTreeBadPair
import Tablet.TashTreeControlledInterchange
import Tablet.TashTreeMinimumBadPair
import Tablet.TashTreePathIndex
import Tablet.TashTreeProperPrefixElementary
import Tablet.TashTreeRankLess
import Tablet.TashTreeSuffixPath
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponentSpanningPath

-- [TABLET NODE: TashTreeMinimumBadPathIndex]
theorem TashTreeMinimumBadPathIndex {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T) :
    2 < TashTreePathIndex G T := by
-- BODY
  sorry
