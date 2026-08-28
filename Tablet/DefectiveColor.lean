import Tablet.BoundaryColorEdges

-- [TABLET NODE: DefectiveColor]
def DefectiveColor {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k)
    (X : Finset V) (alpha : Fin k) : Prop :=
-- BODY
  2 ≤ (BoundaryColorEdges G phi X alpha).card
