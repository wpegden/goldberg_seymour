import Tablet.ChromaticIndexRestrict
import Tablet.Critical

-- [TABLET NODE: CriticalCoreExists]
theorem CriticalCoreExists {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) :
    ∃ F : Finset E,
      ChromaticIndex (RestrictEdges G F) = ChromaticIndex G ∧
      Critical (RestrictEdges G F) := by
-- BODY
  sorry
