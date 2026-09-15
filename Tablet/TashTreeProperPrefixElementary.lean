import Tablet.TashTreeBadPair
import Tablet.TashTreeMinimumBadPair
import Tablet.TashTreePathIndex
import Tablet.TashTreeRankLess
import Tablet.TashTreeSuffixPath
import Tablet.TashkinovTree
import Tablet.TreeSequenceInitialSegment

-- [TABLET NODE: TashTreeProperPrefixElementary]
theorem TashTreeProperPrefixElementary {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T S : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hprefix : TreeSequenceInitialSegment S T) (hproper : S.length < T.length) :
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet S) := by
-- BODY
  sorry
