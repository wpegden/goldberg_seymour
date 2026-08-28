import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder

-- [TABLET NODE: TreeVerticesBefore]
noncomputable def TreeVerticesBefore {V E : Type*} [Fintype V]
    {G : LooplessMultigraph V E} {e0 : E} (T : TreeSequence G e0) (v : V)
    (_hv : v ∈ TreeSequenceVertexSet T) : Finset V := by
-- BODY
  classical
  exact (TreeSequenceVertexSet T).filter fun w => TreeVertexOrder T w v
