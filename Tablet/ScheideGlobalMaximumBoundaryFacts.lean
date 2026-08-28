import Tablet.AdjacentEdges
import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetStronglyClosed
import Tablet.DefectiveColor
import Tablet.DefectiveColors
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.InternalEdges
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideMaximalElementaryClosed
import Tablet.TreeMissingColors

-- [TABLET NODE: ScheideGlobalMaximumBoundaryFacts]
theorem ScheideGlobalMaximumBoundaryFacts {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T) :
    (DefectiveColors G phi (TreeSequenceVertexSet T) = ∅ →
      ColoredVertexSetStronglyClosed G phi (TreeSequenceVertexSet T)) ∧
    (∀ alpha ∈ TreeMissingColors phi T,
      BoundaryColorEdges G phi (TreeSequenceVertexSet T) alpha = ∅) ∧
    (∀ alpha ∈ DefectiveColors G phi (TreeSequenceVertexSet T),
      Odd (BoundaryColorEdges G phi (TreeSequenceVertexSet T) alpha).card ∧
        3 ≤ (BoundaryColorEdges G phi
          (TreeSequenceVertexSet T) alpha).card) := by
-- BODY
  sorry
