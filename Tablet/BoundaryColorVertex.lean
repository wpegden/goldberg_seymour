import Tablet.BoundaryColorEdges
import Tablet.Incident

-- [TABLET NODE: BoundaryColorVertex]
def BoundaryColorVertex {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k)
    (X : Finset V) (delta : Fin k) (v : V) : Prop :=
-- BODY
  v ∈ X ∧ ∃ f ∈ BoundaryColorEdges G phi X delta, Incident G v f
