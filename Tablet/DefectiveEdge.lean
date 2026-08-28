import Tablet.DefectiveColor

-- [TABLET NODE: DefectiveEdge]
def DefectiveEdge {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k)
    (X : Finset V) (f : E) : Prop :=
-- BODY
  ∃ alpha : Fin k,
    DefectiveColor G phi X alpha ∧ f ∈ BoundaryColorEdges G phi X alpha
