import Tablet.GlobalMaximumTriple
import Tablet.KTriple
import Tablet.ScheideDefectiveSwitchEffect
import Tablet.ScheideDefectiveSetup
import Tablet.ScheideReducedConfiguration
import Tablet.ScheideReplacementData
import Tablet.ScheideReplacementPairFixed
import Tablet.ScheideStructuralConfiguration
import Tablet.ScheideStructuralExitsInBase
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: ScheideReplacementMaximum]
theorem ScheideReplacementMaximum {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    let phiD := TwoColorComponentSwap G phi
      (C.gamma (D.gammaIndex d)) d.1 (Sum.inl (D.v0 d))
    IsProperEdgeColoring G phiD ∧ IsOneEdgeUncolored phiD e0 ∧
      GlobalMaximumTriple G k e0 phiD R.replacementTree := by
-- BODY
  sorry
