import Tablet.ColoredVertexSetClosed

-- [TABLET NODE: ColoredVertexSetStronglyClosed]
def ColoredVertexSetStronglyClosed {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k)
    (X : Finset V) : Prop :=
-- BODY
  ColoredVertexSetClosed G phi X ∧
    ∀ {f g c}, f ∈ BoundaryEdges G X → g ∈ BoundaryEdges G X →
      f ≠ g → phi f = some c → phi g ≠ some c
