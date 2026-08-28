import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideGlobalMaximumMissingCounts
import Tablet.TreeFreeColors

-- [TABLET NODE: ScheideGlobalMaximumFourFree]
theorem ScheideGlobalMaximumFourFree {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T) :
    4 ≤ (TreeFreeColors phi T).card := by
-- BODY
  sorry
