import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.GlobalMaximumTriple
import Tablet.IsOneEdgeUncolored
import Tablet.KTriple
import Tablet.MissingColors
import Tablet.ScheideDefectiveSetup
import Tablet.ScheideEnlargedElementary
import Tablet.ScheideEnlargedVertexSet
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideReplacementData
import Tablet.ScheideReplacementMaximum
import Tablet.ScheideReplacementPairsLaminar
import Tablet.ScheideReplacementUnionClosed
import Tablet.ScheideStructuralConfiguration
import Tablet.TashkinovOrder
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper

-- [TABLET NODE: ScheideEnlargedClosed]
theorem ScheideEnlargedClosed {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R : ∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d) :
    ColoredVertexSetClosed G phi (ScheideEnlargedVertexSet R) := by
-- BODY
  sorry
