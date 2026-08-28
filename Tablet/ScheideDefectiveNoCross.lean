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
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.ScheideDefectiveChainPath
import Tablet.ScheideDefectiveSetup
import Tablet.ScheideGlobalMaximumBoundaryFacts
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideGlobalMaximumUnused
import Tablet.ScheideExitVertex
import Tablet.ScheideExitVertices
import Tablet.ScheideReducedConfiguration
import Tablet.ScheideStructuralConfiguration
import Tablet.ScheideStructuralInternalPair
import Tablet.OutsideTreeColorSwap
import Tablet.TashkinovOrder
import Tablet.TashkinovTree
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TreeUsedColors
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ScheideDefectiveNoCross]
theorem ScheideDefectiveNoCross {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C) :
    ∀ d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)},
      ∀ f : E, phi f = some d.1 →
        ¬ (∃ x ∈ ({C.blockVertex (D.gammaIndex d) 0,
                    C.blockVertex (D.gammaIndex d) 1} : Finset V),
          Incident G x f ∧
            ∃ z ∈ TreeSequenceVertexSet T \
                {C.blockVertex (D.gammaIndex d) 0,
                  C.blockVertex (D.gammaIndex d) 1}, Incident G z f) := by
-- BODY
  sorry
