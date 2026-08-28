import Tablet.AbsorbingVertex

-- [TABLET NODE: AbsorbingVertices]
noncomputable def AbsorbingVertices {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) : Finset V := by
-- BODY
  classical
  exact Finset.univ.filter fun v => AbsorbingVertex T phi v
