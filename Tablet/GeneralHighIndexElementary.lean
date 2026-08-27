import Tablet.CriticalCoreExists
import Tablet.ElementaryTransfer
import Tablet.MaximumDegreeRestrict
import Tablet.ThmGS2

-- [TABLET NODE: GeneralHighIndexElementary]
theorem GeneralHighIndexElementary {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E)
    (hG : MaximumDegree G + 2 ≤ ChromaticIndex G) : Elementary G := by
-- BODY
  sorry
