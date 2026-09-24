import Tablet.ScheideDefectiveChainPath
import Tablet.ScheideDefectiveChainPathExists
import Tablet.ScheideDefectiveSwitchEffect
import Tablet.ScheideGlobalMaximumMissingCounts
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideGlobalMaximumUnused
import Tablet.ScheideReplacementData
import Tablet.ScheideReplacementMaximum
import Tablet.ScheideReplacementPairFixed
import Tablet.ScheideStructuralConfiguration
import Tablet.ScheideSymmetricReplacementBoundaryConfiguration
import Tablet.TreeFreeColors

-- [TABLET NODE: ScheideSymmetricReplacementFreePath]
theorem ScheideSymmetricReplacementFreePath {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    let gamma := C.gamma (D.gammaIndex d)
    let phiD := TwoColorComponentSwap G phi gamma d.1 (Sum.inl (D.v0 d))
    ∃ (beta : Fin k) (v z : V)
      (p : (TwoColorIncidenceGraph G phiD gamma beta).Walk
        (Sum.inl v) (Sum.inl z)),
      v ∈ TreeSequenceVertexSet T \
          {C.blockVertex (D.gammaIndex d) 0,
            C.blockVertex (D.gammaIndex d) 1} ∧
      beta ∈ MissingColors G phiD v ∧
      beta ∈ MissingColors G phi v ∧
      beta ∈ TreeFreeColors phiD R.replacementTree ∧
      beta ≠ d.1 ∧ beta ≠ gamma ∧
      ScheideDefectiveChainPath R.replacementTree phiD gamma beta v z p := by
-- BODY
  sorry
