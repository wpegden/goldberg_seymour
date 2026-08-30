import Tablet.AdjacentEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.Degree
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.MaximumDegree
import Tablet.MissingColors
import Tablet.OutsideTreeColorSwap
import Tablet.PresentColors
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequencePreservesTashkinovTree
import Tablet.TashkinovClosure
import Tablet.TashkinovClosureExists
import Tablet.TashkinovTree
import Tablet.TashTree
import Tablet.TreeExitPath
import Tablet.TreeIncidentEdge
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorPathComponent

-- [TABLET NODE: Tchange]
theorem Tchange {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (htriple : KTriple G k e0 phi)
    (hT : TashkinovTree G e0 phi T)
    (hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet T))
    (alpha beta : Fin k)
    (hmissing : alpha ∈ TreeMissingColors phi T ∨
      beta ∈ TreeMissingColors phi T) :
    TreeInterchangeable G T phi alpha beta := by
-- BODY
  sorry
