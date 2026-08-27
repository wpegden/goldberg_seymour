import Tablet.TreeSequence

-- [TABLET NODE: TreeSequenceVertexSet]
noncomputable def TreeSequenceVertexSet {V E : Type*} {G : LooplessMultigraph V E}
    {e0 : E} (T : TreeSequence G e0) : Finset V := by
-- BODY
  classical
  exact Finset.univ.image T.vertex
