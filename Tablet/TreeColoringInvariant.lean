import Tablet.MissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: TreeColoringInvariant]
def TreeColoringInvariant {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (phi pi : PartialEdgeColoring E k) : Prop :=
-- BODY
  (∀ j : Fin T.length, 1 ≤ j.val → pi (T.edge j) = phi (T.edge j)) ∧
    ∀ v ∈ TreeSequenceVertexSet T,
      MissingColors G pi v = MissingColors G phi v
