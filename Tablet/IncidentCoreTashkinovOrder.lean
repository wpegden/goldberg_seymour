import Tablet.IncidentCoreChromaticIndex
import Tablet.IncidentCoreKTriple
import Tablet.IncidentCoreTreeTransport
import Tablet.TashkinovOrder

-- [TABLET NODE: IncidentCoreTashkinovOrder]
theorem IncidentCoreTashkinovOrder {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) :
    TashkinovOrder (IncidentCore G) = TashkinovOrder G := by
-- BODY
  sorry
