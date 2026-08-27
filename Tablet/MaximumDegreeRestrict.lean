import Tablet.MaximumDegree
import Tablet.RestrictEdges

-- [TABLET NODE: MaximumDegreeRestrict]
theorem MaximumDegreeRestrict {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) (F : Finset E) :
    MaximumDegree (RestrictEdges G F) ≤ MaximumDegree G := by
-- BODY
  sorry
