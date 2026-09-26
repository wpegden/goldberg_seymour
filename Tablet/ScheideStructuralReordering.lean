import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.DefectiveColor
import Tablet.DefectiveColors
import Tablet.GlobalMaximumTriple
import Tablet.KTriple
import Tablet.ScheideDefectiveChainPath
import Tablet.ScheideExitVertex
import Tablet.ScheideExitVertices
import Tablet.ScheideStructuralConfiguration
import Tablet.ScheideStructuralReorderingData
import Tablet.ScheideStructuralSelectionData
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: ScheideStructuralReordering]
theorem ScheideStructuralReordering {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideStructuralConfiguration G k e0 phi T)
    (D : ScheideStructuralSelectionData G k e0 phi T C) :
    ∃ T' : TreeSequence G e0,
      Nonempty (ScheideStructuralReorderingData G k e0 phi T C D T') := by
-- BODY
  sorry
