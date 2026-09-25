import Tablet.AdjacentEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.ScheideDefectiveSetup
import Tablet.ScheideEnlargedClosed
import Tablet.ScheideEnlargedElementary
import Tablet.ScheideEnlargedVertexSet
import Tablet.ScheideLastExitPath
import Tablet.ScheideReducedConfiguration
import Tablet.ScheideStructuralConfiguration
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorIncidenceDegreeAtMostTwo

-- [TABLET NODE: ScheideTwoColorLastExitPath]
theorem ScheideTwoColorLastExitPath {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R : ∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d)
    (alpha : Fin k)
    (hpresent : ∀ v ∈ ScheideEnlargedVertexSet R,
      alpha ∈ PresentColors G phi v) :
    Nonempty (ScheideLastExitPath G k e0 phi T C D R alpha) := by
-- BODY
  sorry
