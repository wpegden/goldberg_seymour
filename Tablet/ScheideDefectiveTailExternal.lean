import Tablet.OutsideTreeColorSwap
import Tablet.ScheideDefectiveNoCross
import Tablet.ScheideGlobalMaximumMissingCounts
import Tablet.ScheideStructuralExitsInBase
import Tablet.ScheideStructuralInternalPair
import Tablet.TwoColorComponentSwapProper

-- [TABLET NODE: ScheideDefectiveTailExternal]
theorem ScheideDefectiveTailExternal {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C) :
    ∀ d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)},
      ∀ w ∈ TreeSequenceVertexSet T,
        Sum.inl w ∈ TwoColorComponent G phi (C.gamma (D.gammaIndex d)) d.1
          (Sum.inl (D.v0 d)) →
        w = D.v0 d := by
-- BODY
  sorry
