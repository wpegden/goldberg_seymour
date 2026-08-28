import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideReplacementMaximum
import Tablet.ScheideReplacementPairFixed

open scoped Sym2

-- [TABLET NODE: ScheideReplacementInternalMissing]
theorem ScheideReplacementInternalMissing {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    ∀ alpha : Fin k, alpha ≠ C.gamma (D.gammaIndex d) →
      (∃ z ∈ TreeSequenceVertexSet T \
          {C.blockVertex (D.gammaIndex d) 0,
            C.blockVertex (D.gammaIndex d) 1},
        alpha ∈ MissingColors G phi z) →
      ∃ f : E, phi f = some alpha ∧ G.ends f = s(R.u1, R.u2) := by
-- BODY
  sorry
