import Tablet.BoundaryEdges
import Tablet.MissingColors

-- [TABLET NODE: ColoredVertexSetClosed]
def ColoredVertexSetClosed {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k)
    (X : Finset V) : Prop :=
-- BODY
  ∀ {f c v}, f ∈ BoundaryEdges G X → v ∈ X →
    phi f = some c → c ∉ MissingColors G phi v
