import Tablet.KTriple
import Tablet.TashTreeProperPrefixElementary
import Tablet.TreeFreeColors
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequencePrefix
import Tablet.TreeUsedColors

-- [TABLET NODE: TashTreeFourUnusedColors]
theorem TashTreeFourUnusedColors {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (q : ℕ) (hq : 1 ≤ q) (hqt : q < T.length) :
    4 ≤ (TreeFreeColors phi
      (TreeSequencePrefix T q hq (Nat.le_of_lt hqt))).card := by
-- BODY
  sorry
