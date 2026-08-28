import Tablet.AdjacentEdges
import Tablet.BalancedGlobalMaximumTriple
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.Degree
import Tablet.GlobalMaximumTriple
import Tablet.GlobalMaximumTripleExists
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.MaximumDegree
import Tablet.MissingColors
import Tablet.NormalGlobalMaximumTriple
import Tablet.PresentColors
import Tablet.ScheideBalancedExists
import Tablet.ScheideExitNoFree
import Tablet.ScheideExitVertex
import Tablet.ScheideExitVertices
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideGraphHeightOdd
import Tablet.ScheideHeightFiveGammaEdges
import Tablet.ScheideHeightFiveOutsideLinks
import Tablet.ScheideKempePathHeightBound
import Tablet.ScheideLargeHeightElementary
import Tablet.ScheideSmallHeightElementary
import Tablet.ScheideStructuralConfiguration
import Tablet.ScheideTrunkRotationPreserves
import Tablet.TashkinovTree
import Tablet.TreeFreeColors
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TreeUsedColors
import Tablet.TrunkRotation
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper

-- [TABLET NODE: ScheideOrderNineStructuralConfiguration]
theorem ScheideOrderNineStructuralConfiguration {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ)
    (hcritical : Critical G) (hindex : ChromaticIndex G = k + 1)
    (hdegree : MaximumDegree G + 1 ≤ k)
    (hnoisolated : ∀ v : V, ∃ e : E, Incident G v e)
    (hnonelementary : ¬ Elementary G) (horder : TashkinovOrder G < 11) :
    ∃ (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0),
      Nonempty (ScheideStructuralConfiguration G k e0 phi T) := by
-- BODY
  sorry
