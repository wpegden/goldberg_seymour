import Tablet.ChromaticIndexSpec
import Tablet.MaximumDegree

-- [TABLET NODE: MaximumDegreeLowerBound]
theorem MaximumDegreeLowerBound {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) : MaximumDegree G ≤ ChromaticIndex G := by
-- BODY
  sorry
