import Tablet.KTriple
import Tablet.TashTreeControlledInterchange
import Tablet.TashTreeMinimumBadPair
import Tablet.TashTreeProperPrefixElementary
import Tablet.TashTreeSuffixPath

-- [TABLET NODE: TashTreeMinimumBadPathIndex]
theorem TashTreeMinimumBadPathIndex {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T) :
    2 < TashTreePathIndex G T := by
-- BODY
  sorry
