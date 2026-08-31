import Tablet.TreeSequence

-- [TABLET NODE: TreeSequenceEdgeSet]
noncomputable def TreeSequenceEdgeSet {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {e0 : E} (T : TreeSequence G e0) : Finset E := by
-- BODY
  classical
  exact Finset.univ.image T.edge
