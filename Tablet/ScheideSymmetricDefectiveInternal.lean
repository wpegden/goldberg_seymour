import Tablet.ScheideDefectiveChainBoundaryEdges
import Tablet.ScheideDefectiveChainPathExists
import Tablet.ScheideReplacementInternalMissing
import Tablet.ScheideStructuralExitsInBase

open scoped Sym2

-- [TABLET NODE: ScheideSymmetricDefectiveInternal]
theorem ScheideSymmetricDefectiveInternal {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    (∃ f : E, phi f = some d.1 ∧
      G.ends f = s(C.blockVertex (D.gammaIndex d) 0,
        C.blockVertex (D.gammaIndex d) 1)) ∧
    ∃ f : E, phi f = some (C.gamma (D.gammaIndex d)) ∧
      G.ends f = s(R.u1, R.u2) := by
-- BODY
  sorry
