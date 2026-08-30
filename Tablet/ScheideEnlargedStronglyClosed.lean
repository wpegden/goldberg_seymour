import Tablet.AdjacentEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetStronglyClosed
import Tablet.DefectiveColors
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.InternalEdges
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.ScheideDefectiveChainPath
import Tablet.ScheideDefectiveSetup
import Tablet.ScheideDefectiveSwitchEffect
import Tablet.ScheideEnlargedClosed
import Tablet.ScheideEnlargedVertexSet
import Tablet.ScheideExitVertex
import Tablet.ScheideExitVertices
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideReducedConfiguration
import Tablet.ScheideReplacementData
import Tablet.ScheideReplacementMaximum
import Tablet.ScheideReplacementPairsLaminar
import Tablet.ScheideReplacementUnionClosed
import Tablet.ScheideSingleBoundaryCrossing
import Tablet.ScheideStructuralConfiguration
import Tablet.ScheideStructuralExitsInBase
import Tablet.ScheideSymmetricDefectiveInternal
import Tablet.TashkinovOrder
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ScheideEnlargedStronglyClosed]
theorem ScheideEnlargedStronglyClosed {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R : ∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d) :
    ColoredVertexSetStronglyClosed G phi (ScheideEnlargedVertexSet R) := by
-- BODY
  sorry
