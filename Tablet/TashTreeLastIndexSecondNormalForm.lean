import Tablet.IsOneEdgeUncolored
import Tablet.KTriple
import Tablet.MissingColorIncidenceEndpoint
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.TashTreeControlledInterchange
import Tablet.TashTreeBadPair
import Tablet.TashTreeMinimumBadPair
import Tablet.TashTreePathIndex
import Tablet.TashTreeProperPrefixElementary
import Tablet.TreeSequence
import Tablet.TreeUsedColors
import Tablet.TwoColorComponentSpanningPath

-- [TABLET NODE: TashTreeLastIndexSecondNormalForm]
theorem TashTreeLastIndexSecondNormalForm {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : 2 < TashTreePathIndex G T)
    (hlast : TashTreePathIndex G T = T.length)
    (beta : Fin k) (j : Fin (T.length + 1))
    (hj : j.val + 2 ≤ T.length)
    (hbj : beta ∈ MissingColors G phi (T.vertex j))
    (hblast : beta ∈ MissingColors G phi (T.vertex (Fin.last T.length)))
    (hbunused : beta ∉ TreeUsedColors phi T) :
    ∃ (phi₂ : PartialEdgeColoring E k) (gamma : Fin k)
        (r : Fin T.length) (p : Fin (T.length + 1)),
      r.val + 1 = T.length ∧ p.val + 1 = T.length ∧
        TashTreeMinimumBadPair G k e0 phi₂ T ∧
        phi₂ (T.edge r) = some gamma ∧
        gamma ∈ PresentColors G phi₂ (T.vertex p) := by
-- BODY
  sorry
