import Tablet.ChromaticIndexSpec
import Tablet.ProperColoringRestricts

-- [TABLET NODE: ChromaticIndexRestrict]
theorem ChromaticIndexRestrict {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) (F : Finset E) :
    ChromaticIndex (RestrictEdges G F) ≤ ChromaticIndex G := by
-- BODY
  sorry
