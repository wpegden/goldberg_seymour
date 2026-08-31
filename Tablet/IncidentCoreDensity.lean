import Tablet.DensityCeil
import Tablet.DensityValue
import Tablet.EligibleOddSet
import Tablet.IncidentCoreInternalEdges

-- [TABLET NODE: IncidentCoreDensity]
theorem IncidentCoreDensity {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) :
    DensityCeil (IncidentCore G) ≤ DensityCeil G := by
-- BODY
  sorry
