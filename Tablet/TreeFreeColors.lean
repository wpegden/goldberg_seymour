import Tablet.TreeMissingColors
import Tablet.TreeUsedColors

-- [TABLET NODE: TreeFreeColors]
noncomputable def TreeFreeColors {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) : Finset (Fin k) := by
-- BODY
  classical
  exact TreeMissingColors phi T \ TreeUsedColors phi T
