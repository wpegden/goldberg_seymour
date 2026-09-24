import Tablet.DefectiveColors
import Tablet.ScheideDefectiveSetup
import Tablet.ScheideDefectiveSwitchEffect
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideReplacementData
import Tablet.ScheideReplacementMaximum
import Tablet.ScheideReplacementPairFixed
import Tablet.ScheideStructuralConfiguration
import Tablet.ScheideStructuralExitsInBase
import Tablet.TreeSequence

open scoped Sym2

-- [TABLET NODE: ScheideSymmetricReplacementBoundaryConfiguration]
theorem ScheideSymmetricReplacementBoundaryConfiguration {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    let gamma := C.gamma (D.gammaIndex d)
    let phiD := TwoColorComponentSwap G phi gamma d.1 (Sum.inl (D.v0 d))
    let Xd := TreeSequenceVertexSet R.replacementTree
    let Z := TreeSequenceVertexSet T \
      {C.blockVertex (D.gammaIndex d) 0,
        C.blockVertex (D.gammaIndex d) 1}
    gamma ∈ DefectiveColors G phiD Xd ∧
      phiD (D.f0 d) = some gamma ∧
      phiD (C.blockEdge (D.gammaIndex d) 0) = some gamma ∧
      phiD (C.blockEdge (D.gammaIndex d) 1) = some gamma ∧
      D.f0 d ≠ C.blockEdge (D.gammaIndex d) 0 ∧
      D.f0 d ≠ C.blockEdge (D.gammaIndex d) 1 ∧
      C.blockEdge (D.gammaIndex d) 0 ≠
        C.blockEdge (D.gammaIndex d) 1 ∧
      ∀ f : E,
        (phiD f = some gamma ∧
          ∃ v ∈ Z, ∃ w ∉ Xd, G.ends f = s(v, w)) ↔
        f = D.f0 d ∨
          f = C.blockEdge (D.gammaIndex d) 0 ∨
          f = C.blockEdge (D.gammaIndex d) 1 := by
-- BODY
  sorry
