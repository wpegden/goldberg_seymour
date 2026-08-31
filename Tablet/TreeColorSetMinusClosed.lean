import Tablet.TreeColorSetClosed
import Tablet.TreeMissingColors

-- [TABLET NODE: TreeColorSetMinusClosed]
def TreeColorSetMinusClosed {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) {k : ℕ} {e0 : E}
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : Finset (Fin k)) : Prop :=
-- BODY
  TreeColorSetClosed G phi T (TreeMissingColors phi T \ C)
