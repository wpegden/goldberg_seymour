import Tablet.BoundaryEdges
import Tablet.ClosedSetTwoColorComponentAvoidance
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.LooplessMultigraph
import Tablet.ScheideDefectiveSwitchEffect
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideReplacementInternalMissing
import Tablet.ScheideReplacementMaximum
import Tablet.ScheideReplacementPairFixed
import Tablet.ScheideStructuralExitsInBase
import Tablet.ScheideSymmetricDefectiveInternal
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceGraph

open scoped Sym2

-- [TABLET NODE: ScheideDeletedMissingReplacementInternal]
theorem ScheideDeletedMissingReplacementInternal {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    ∀ alpha : Fin k,
      (alpha ∈ MissingColors G phi (C.blockVertex (D.gammaIndex d) 0) ∨
        alpha ∈ MissingColors G phi (C.blockVertex (D.gammaIndex d) 1)) →
      ∃ f : E, phi f = some alpha ∧ G.ends f = s(R.u1, R.u2) := by
-- BODY
  sorry
