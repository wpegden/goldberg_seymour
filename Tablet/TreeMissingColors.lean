import Tablet.MissingColors
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: TreeMissingColors]
noncomputable def TreeMissingColors {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) : Finset (Fin k) := by
-- BODY
  classical
  exact (TreeSequenceVertexSet T).biUnion fun v => MissingColors G phi v
