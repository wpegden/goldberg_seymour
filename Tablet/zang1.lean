import Tablet.AdjacentEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetStronglyClosed
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.PartialEdgeColoring
import Tablet.PresentColors
import Tablet.StableColoring
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.sc1

-- [TABLET NODE: zang1]
theorem zang1 {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) {k : ℕ}
    (e0 : E) (T : TreeSequence G e0) (C : Finset (Fin k))
    (phi pi : PartialEdgeColoring E k)
    (hproperPhi : IsProperEdgeColoring G phi)
    (honePhi : IsOneEdgeUncolored phi e0)
    (hproperPi : IsProperEdgeColoring G pi)
    (honePi : IsOneEdgeUncolored pi e0)
    (hodd : Odd (TreeSequenceVertexSet T).card)
    (hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet T))
    (hnotstrong : ¬ ColoredVertexSetStronglyClosed G phi (TreeSequenceVertexSet T))
    (hstable : StableColoring T C phi pi) :
    ColoredVertexSetClosed G pi (TreeSequenceVertexSet T) ∧
      ¬ ColoredVertexSetStronglyClosed G pi (TreeSequenceVertexSet T) := by
-- BODY
  sorry
