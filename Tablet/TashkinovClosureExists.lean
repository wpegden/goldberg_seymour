import Tablet.BoundaryEdges
import Tablet.TashkinovClosure

-- [TABLET NODE: TashkinovClosureExists]
theorem TashkinovClosureExists {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) :
    ∃ T' : TreeSequence G e0, TashkinovClosure phi T T' := by
-- BODY
  sorry
