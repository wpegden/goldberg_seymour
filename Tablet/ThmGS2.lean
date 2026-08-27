import Tablet.Critical
import Tablet.Elementary
import Tablet.MaximumDegree
import Tablet.TashTree
import Tablet.TashkinovOrder
import Tablet.TreeSequencePrefix
import Tablet.egraph2

-- [TABLET NODE: ThmGS2]
theorem ThmGS2 {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (hG : MaximumDegree G + 2 ≤ ChromaticIndex G)
    (hcrit : Critical G) : Elementary G := by
-- BODY
  sorry
