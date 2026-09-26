import Tablet.ColoredVertexSetElementary
import Tablet.MissingColors
import Tablet.ScheideExitVertices
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideStructuralConfiguration
import Tablet.ScheideStructuralSelectionData
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: ScheideStructuralSelection]
theorem ScheideStructuralSelection {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideStructuralConfiguration G k e0 phi T) :
    Nonempty (ScheideStructuralSelectionData G k e0 phi T C) := by
-- BODY
  sorry
