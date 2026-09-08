import Tablet.CriticalCoreExists
import Tablet.ElementaryTransfer
import Tablet.HierarchySituationThreeComponentIntersectionShortening
import Tablet.HierarchySituationTwoImpossible
import Tablet.MaximumDegreeRestrict
import Tablet.ThmGS2

-- [TABLET NODE: GeneralHighIndexElementary]
theorem GeneralHighIndexElementary {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E)
    (hG : MaximumDegree G + 2 ≤ ChromaticIndex G) : Elementary G := by
-- BODY
  obtain ⟨F, hχ, hcrit⟩ := CriticalCoreExists G
  apply ElementaryTransfer G F hχ
  refine ThmGS2 (RestrictEdges G F) ?_ hcrit
  have hdeg := MaximumDegreeRestrict G F
  omega
