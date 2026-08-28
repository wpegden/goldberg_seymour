import Tablet.BoundaryEdges
import Tablet.TashkinovClosure

-- [TABLET NODE: TashkinovClosureVertexSetUnique]
theorem TashkinovClosureVertexSetUnique {V E : Type*}
    [Fintype V] [Fintype E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (phi : PartialEdgeColoring E k) (T T₁ T₂ : TreeSequence G e0)
    (h₁ : TashkinovClosure phi T T₁) (h₂ : TashkinovClosure phi T T₂) :
    TreeSequenceVertexSet T₁ = TreeSequenceVertexSet T₂ := by
-- BODY
  sorry
