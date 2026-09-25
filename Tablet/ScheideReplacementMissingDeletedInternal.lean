import Tablet.ClosedSetTwoColorComponentAvoidance
import Tablet.ScheideDefectiveSwitchEffect
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideReplacementMaximum
import Tablet.ScheideReplacementPairFixed
import Tablet.ScheideStructuralInternalPair
import Tablet.ScheideSymmetricDefectiveInternal
import Tablet.TwoColorComponentSwapProper

open scoped Sym2

-- [TABLET NODE: ScheideReplacementMissingDeletedInternal]
theorem ScheideReplacementMissingDeletedInternal {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    ∀ alpha : Fin k,
      (alpha ∈ MissingColors G phi R.u1 ∨ alpha ∈ MissingColors G phi R.u2) →
      ∃ f : E, phi f = some alpha ∧
        G.ends f = s(C.blockVertex (D.gammaIndex d) 0,
          C.blockVertex (D.gammaIndex d) 1) := by
-- BODY
  sorry
