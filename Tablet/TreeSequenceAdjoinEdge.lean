import Tablet.TreeSequenceInitialSegment

-- [TABLET NODE: TreeSequenceAdjoinEdge]
def TreeSequenceAdjoinEdge {V E : Type*} {G : LooplessMultigraph V E}
    {e0 : E} (T : TreeSequence G e0) (f : E) (Tplus : TreeSequence G e0) : Prop :=
-- BODY
  ∃ hlen : Tplus.length = T.length + 1,
    TreeSequenceInitialSegment T Tplus ∧
      Tplus.edge (Fin.cast hlen.symm (Fin.last T.length)) = f
