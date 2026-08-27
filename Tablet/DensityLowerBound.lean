import Tablet.ChromaticIndexSpec
import Tablet.DensityCeil

-- [TABLET NODE: DensityLowerBound]
theorem DensityLowerBound {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) : DensityCeil G ≤ ChromaticIndex G := by
-- BODY
  sorry
