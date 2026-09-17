import Tablet.ColoredVertexSetElementary
import Tablet.MissingColors
import Tablet.TashTreeBadPair
import Tablet.TashTreeMinimumBadPair
import Tablet.TashTreePathIndex
import Tablet.TashTreeProperPrefixElementary
import Tablet.TreeSequence
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: TashTreeRhoOneRepeatedColor]
theorem TashTreeRhoOneRepeatedColor {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hlen : 2 ≤ T.length) (hq : TashTreePathIndex G T = 1) :
    ∃ beta : Fin k, ∃ i : Fin T.length,
      beta ∈ MissingColors G phi (T.vertex i.castSucc) ∧
      beta ∈ MissingColors G phi (T.vertex (Fin.last T.length)) := by
-- BODY
  sorry
