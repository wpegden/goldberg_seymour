import Tablet.ScheideEnlargedClosed
import Tablet.ScheideSingleBoundaryCrossing
import Tablet.ScheideSymmetricDefectiveInternal
import Tablet.TwoColorComponentSwapProper

-- [TABLET NODE: ScheideEnlargedStronglyClosed]
theorem ScheideEnlargedStronglyClosed {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R : ∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d) :
    ColoredVertexSetStronglyClosed G phi (ScheideEnlargedVertexSet R) := by
-- BODY
  sorry
