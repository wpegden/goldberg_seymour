import Tablet.TashTreeControlledInterchange
import Tablet.TashTreeFourUnusedColors
import Tablet.TashTreeMinimumBadPair
import Tablet.TashTreeMinimumBadPathIndex
import Tablet.TashTreePathIndex
import Tablet.TwoColorComponentSwapProper

-- [TABLET NODE: TashTreeCasePathIndexLast]
theorem TashTreeCasePathIndexLast {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : 2 < TashTreePathIndex G T)
    (hlast : TashTreePathIndex G T = T.length) : False := by
-- BODY
  sorry
