import Tablet.ColoredVertexSetElementary
import Tablet.MissingColorIncidenceEndpoint
import Tablet.MissingColors
import Tablet.TashTreeBadPair
import Tablet.TashTreeControlledInterchange
import Tablet.TashTreeFourUnusedColors
import Tablet.TashTreeMinimumBadPair
import Tablet.TashTreeProperPrefixElementary
import Tablet.TashkinovTree
import Tablet.TreeColorUnusedThrough
import Tablet.TreeFreeColors
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.TreeUsedColors
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwapMissingBehavior

-- [TABLET NODE: TashTreeEarlyBetaNormalization]
theorem TashTreeEarlyBetaNormalization {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : 2 < TashTreePathIndex G T)
    (hbefore : TashTreePathIndex G T < T.length)
    (hnone : ¬ ∃ alpha : Fin k, ∃ i : Fin (T.length + 1),
      TashTreePathIndex G T ≤ i.val ∧ i.val < T.length ∧
      alpha ∈ MissingColors G phi (T.vertex i) ∧
      alpha ∈ MissingColors G phi (T.vertex (Fin.last T.length))) :
    ∃ (phi' : PartialEdgeColoring E k) (beta : Fin k)
        (i : Fin (T.length + 1)),
      TashTreeMinimumBadPair G k e0 phi' T ∧
      i.val + 2 ≤ TashTreePathIndex G T ∧
      beta ∈ MissingColors G phi' (T.vertex i) ∧
      beta ∈ MissingColors G phi' (T.vertex (Fin.last T.length)) ∧
      ¬ ∃ alpha : Fin k, ∃ s : Fin (T.length + 1),
        TashTreePathIndex G T ≤ s.val ∧ s.val < T.length ∧
        alpha ∈ MissingColors G phi' (T.vertex s) ∧
        alpha ∈ MissingColors G phi'
          (T.vertex (Fin.last T.length)) := by
-- BODY
  sorry
