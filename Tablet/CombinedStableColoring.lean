import Tablet.StableColoring

-- [TABLET NODE: CombinedStableColoring]
def CombinedStableColoring {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (Tn R : TreeSequence G e0) (D : Finset (Fin k))
    (phi sigma : PartialEdgeColoring E k) : Prop :=
-- BODY
  StableColoring Tn D phi sigma ∧ StableColoring R ∅ phi sigma
