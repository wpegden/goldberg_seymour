import Tablet.AdjacentEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.OutsideTreeColorSwap
import Tablet.PresentColors
import Tablet.StableColoring
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: OutsideTreeColorSwapStable]
theorem OutsideTreeColorSwapStable {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (C : Finset (Fin k))
    (phi : PartialEdgeColoring E k) (alpha beta : Fin k)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet T))
    (halpha : alpha ∈ TreeMissingColors phi T)
    (hbeta : beta ∈ TreeMissingColors phi T)
    (hdistinct : alpha ≠ beta) :
    let psi := OutsideTreeColorSwap T phi alpha beta
    IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0 ∧
      StableColoring T C phi psi ∧
      ∀ f : E, TreeIncidentEdge T f → psi f = phi f := by
-- BODY
  sorry
