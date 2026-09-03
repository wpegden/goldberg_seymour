import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetElementary
import Tablet.Incident
import Tablet.IsProperEdgeColoring
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.TreeInterchangeable
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorPathComponent

-- [TABLET NODE: ElementarySingleBoundaryInterchangeable]
lemma ElementarySingleBoundaryInterchangeable {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) {k : ℕ} {e0 : E}
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (alpha beta : Fin k)
    (hproper : IsProperEdgeColoring G phi)
    (helementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet T))
    (halpha : BoundaryColorEdges G phi
      (TreeSequenceVertexSet T) alpha = {})
    (hbeta : (BoundaryColorEdges G phi
      (TreeSequenceVertexSet T) beta).card ≤ 1) :
    TreeInterchangeable G T phi alpha beta := by
-- BODY
  sorry
