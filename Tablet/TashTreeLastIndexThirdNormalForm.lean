import Tablet.ColoredVertexSetElementary
import Tablet.KTriple
import Tablet.MissingColorIncidenceEndpoint
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.TashTreeBadPair
import Tablet.TashTreeControlledInterchange
import Tablet.TashTreeFourUnusedColors
import Tablet.TashTreeMinimumBadPair
import Tablet.TashTreePathIndex
import Tablet.TashTreeProperPrefixElementary
import Tablet.TashkinovTree
import Tablet.TreeFreeColors
import Tablet.TreeSequence
import Tablet.TreeSequencePrefix
import Tablet.TreeUsedColors
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapMissingBehavior

-- [TABLET NODE: TashTreeLastIndexThirdNormalForm]
theorem TashTreeLastIndexThirdNormalForm {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : 2 < TashTreePathIndex G T)
    (hlast : TashTreePathIndex G T = T.length)
    (gamma : Fin k) (r : Fin T.length) (p : Fin (T.length + 1))
    (hr : r.val + 1 = T.length) (hp : p.val + 1 = T.length)
    (hrgamma : phi (T.edge r) = some gamma)
    (hpgamma : gamma ∈ PresentColors G phi (T.vertex p)) :
    ∃ (phi₃ : PartialEdgeColoring E k) (beta : Fin k)
        (j : Fin (T.length + 1)),
      TashTreeMinimumBadPair G k e0 phi₃ T ∧
        phi₃ (T.edge r) = some gamma ∧
        gamma ∈ PresentColors G phi₃ (T.vertex p) ∧
        j.val + 2 ≤ T.length ∧
        beta ∈ MissingColors G phi₃ (T.vertex j) ∧
        beta ∈ MissingColors G phi₃ (T.vertex (Fin.last T.length)) := by
-- BODY
  sorry
