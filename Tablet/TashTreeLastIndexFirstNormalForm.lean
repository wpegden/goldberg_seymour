import Tablet.ColoredVertexSetElementary
import Tablet.MissingColorIncidenceEndpoint
import Tablet.MissingColors
import Tablet.TashTreeBadPair
import Tablet.TashTreeControlledInterchange
import Tablet.TashTreeDisjointComponentNormalization
import Tablet.TashTreeFourUnusedColors
import Tablet.TashTreeLastIndexIntersectionShortening
import Tablet.TashTreeMinimumBadPair
import Tablet.TashTreePathIndex
import Tablet.TashTreeProperPrefixElementary
import Tablet.TreeFreeColors
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequencePrefix
import Tablet.TreeUsedColors
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapMissingBehavior

-- [TABLET NODE: TashTreeLastIndexFirstNormalForm]
theorem TashTreeLastIndexFirstNormalForm {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : 2 < TashTreePathIndex G T)
    (hlast : TashTreePathIndex G T = T.length) :
    ∃ (phi₁ : PartialEdgeColoring E k) (beta : Fin k)
        (j : Fin (T.length + 1)),
      TashTreeMinimumBadPair G k e0 phi₁ T ∧
        j.val + 2 ≤ T.length ∧
        beta ∈ MissingColors G phi₁ (T.vertex j) ∧
        beta ∈ MissingColors G phi₁ (T.vertex (Fin.last T.length)) ∧
        beta ∉ TreeUsedColors phi₁ T := by
-- BODY
  sorry
