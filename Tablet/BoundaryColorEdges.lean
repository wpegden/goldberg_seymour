import Tablet.BoundaryEdges
import Tablet.PartialEdgeColoring

-- [TABLET NODE: BoundaryColorEdges]
noncomputable def BoundaryColorEdges {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k)
    (X : Finset V) (alpha : Fin k) : Finset E := by
-- BODY
  classical
  exact (BoundaryEdges G X).filter fun f => phi f = some alpha
