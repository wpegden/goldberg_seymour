import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.DefectiveColors
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.ScheideDefectiveSetup
import Tablet.ScheideDefectiveSwitchEffect
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideReducedConfiguration
import Tablet.ScheideReplacementData
import Tablet.ScheideReplacementInternalMissing
import Tablet.ScheideReplacementMaximum
import Tablet.ScheideReplacementPairFixed
import Tablet.ScheideStructuralConfiguration
import Tablet.ScheideStructuralExitsInBase
import Tablet.ScheideStructuralInternalPair
import Tablet.ScheideSymmetricDefectiveInternal
import Tablet.TashkinovOrder
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper

open scoped Sym2

-- [TABLET NODE: ScheideSymmetricMissingInternal]
theorem ScheideSymmetricMissingInternal {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    (∀ alpha : Fin k,
      (alpha ∈ MissingColors G phi R.u1 ∨ alpha ∈ MissingColors G phi R.u2) →
      ∃ f : E, phi f = some alpha ∧
        G.ends f = s(C.blockVertex (D.gammaIndex d) 0,
          C.blockVertex (D.gammaIndex d) 1)) ∧
    ∀ alpha : Fin k,
      (alpha ∈ MissingColors G phi (C.blockVertex (D.gammaIndex d) 0) ∨
        alpha ∈ MissingColors G phi (C.blockVertex (D.gammaIndex d) 1)) →
      ∃ f : E, phi f = some alpha ∧ G.ends f = s(R.u1, R.u2) := by
-- BODY
  sorry
