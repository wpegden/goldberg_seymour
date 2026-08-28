import Tablet.AdjacentEdges
import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.DefectiveColors
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.MissingColors
import Tablet.OutsideTreeColorSwap
import Tablet.PresentColors
import Tablet.ScheideDefectiveChainBoundaryEdges
import Tablet.ScheideDefectiveChainDepartureReturn
import Tablet.ScheideDefectiveChainLastReturnNoFree
import Tablet.ScheideDefectiveChainPath
import Tablet.ScheideDepartureReturn
import Tablet.ScheideExitVertex
import Tablet.ScheideExitVertexTreeExit
import Tablet.ScheideExitVertices
import Tablet.ScheideGlobalMaximumBoundaryFacts
import Tablet.ScheideGlobalMaximumOrder
import Tablet.TashkinovTree
import Tablet.TreeFreeColors
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TreeUsedColors
import Tablet.TwoColorComponent
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ScheideExitNoFree]
theorem ScheideExitNoFree {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T) :
    ∀ v ∈ ScheideExitVertices T phi,
      Disjoint (MissingColors G phi v) (TreeFreeColors phi T) := by
-- BODY
  sorry
