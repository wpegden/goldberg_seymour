import Tablet.ColoredVertexSetElementary
import Tablet.KTriple
import Tablet.MissingColorIncidenceEndpoint
import Tablet.MissingColors
import Tablet.MissingColorsNonemptyOfMaximumDegree
import Tablet.PresentColors
import Tablet.TashTreeBadPair
import Tablet.TashTreeControlledInterchange
import Tablet.TashTreeMinimumBadPair
import Tablet.TashTreePathIndex
import Tablet.TashTreeProperPrefixElementary
import Tablet.TashTreeSuffixPath
import Tablet.TashkinovTree
import Tablet.TreeColorUnusedThrough
import Tablet.TreeSequence
import Tablet.TreeSequencePrefix
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwapMissingBehavior

-- [TABLET NODE: TashTreeRhoOneAdvance]
theorem TashTreeRhoOneAdvance {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : TashTreePathIndex G T = 1) (beta : Fin k)
    (i : Fin T.length) (hiNext : i.val + 1 < T.length)
    (hi : beta ∈ MissingColors G phi (T.vertex i.castSucc))
    (hlast : beta ∈ MissingColors G phi
      (T.vertex (Fin.last T.length))) :
    ∃ phi' : PartialEdgeColoring E k,
      TashTreeMinimumBadPair G k e0 phi' T ∧
      beta ∈ MissingColors G phi' (T.vertex i.succ) ∧
      beta ∈ MissingColors G phi'
        (T.vertex (Fin.last T.length)) := by
-- BODY
  sorry
