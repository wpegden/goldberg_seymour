import Tablet.DensityCeil
import Tablet.RestrictEdges

-- [TABLET NODE: DensityMonotone]
theorem DensityMonotone {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) (F : Finset E) :
    DensityCeil (RestrictEdges G F) ≤ DensityCeil G := by
-- BODY
  sorry
