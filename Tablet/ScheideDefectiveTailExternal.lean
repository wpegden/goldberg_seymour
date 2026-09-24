import Tablet.AdjacentEdges
import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.DefectiveColors
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.InternalEdges
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.OutsideTreeColorSwap
import Tablet.PartialEdgeColoring
import Tablet.PresentColors
import Tablet.ScheideDefectiveChainPath
import Tablet.ScheideDefectiveNoCross
import Tablet.ScheideDefectiveLastReturnExists
import Tablet.ScheideDefectiveReturnContradiction
import Tablet.ScheideDefectiveSetup
import Tablet.ScheideGlobalMaximumMissingCounts
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideGlobalMaximumUnused
import Tablet.ScheideExitVertex
import Tablet.ScheideExitVertices
import Tablet.ScheideReducedConfiguration
import Tablet.ScheideStructuralConfiguration
import Tablet.ScheideStructuralExitsInBase
import Tablet.ScheideStructuralInternalPair
import Tablet.TashkinovOrder
import Tablet.TashkinovTree
import Tablet.TreeIncidentEdge
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TreeUsedColors
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ScheideDefectiveTailExternal]
theorem ScheideDefectiveTailExternal {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C) :
    ∀ d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)},
      ∀ w ∈ TreeSequenceVertexSet T,
        Sum.inl w ∈ TwoColorComponent G phi (C.gamma (D.gammaIndex d)) d.1
          (Sum.inl (D.v0 d)) →
        w = D.v0 d := by
-- BODY
  intro d w hw hcomponent
  by_contra hne
  obtain ⟨R⟩ := ScheideDefectiveLastReturnExists
    G k e0 phi T C D d w hw hcomponent hne
  exact ScheideDefectiveReturnContradiction G k e0 phi T C D d R
