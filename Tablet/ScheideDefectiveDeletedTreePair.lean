import Tablet.OutsideTreeColorSwap
import Tablet.GlobalMaximumTriple
import Tablet.IsOneEdgeUncolored
import Tablet.KTriple
import Tablet.MissingColors
import Tablet.ScheideDefectiveReturnData
import Tablet.ScheideDefectiveSecondTerminalComponent
import Tablet.ScheideDefectiveTerminalComponent
import Tablet.ScheideGlobalMaximumUnused
import Tablet.ScheideReducedConfiguration
import Tablet.ScheideSelectedBlockDeletion
import Tablet.ScheideStructuralExitsInBase
import Tablet.TashkinovTree
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceBoundaryEdgeAppendExists
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TreeUsedColors
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.TwoColorComponentSwapProper

-- [TABLET NODE: ScheideDefectiveDeletedTreePair]
theorem ScheideDefectiveDeletedTreePair {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideDefectiveReturnData G k e0 phi T C D d) :
    let gamma := C.gamma (D.gammaIndex d)
    let gammaJ := C.gamma R.blockIndex
    let phi1 := OutsideTreeColorSwap T phi D.alpha0 gamma
    let phi2 := TwoColorComponentSwap G phi1 gamma d.1 (Sum.inl (D.v0 d))
    let psi1 := OutsideTreeColorSwap T phi gamma gammaJ
    let psi2 := TwoColorComponentSwap G psi1 gammaJ d.1 (Sum.inl R.v1)
    ∃ Sgamma SgammaJ : TreeSequence G e0,
      TashkinovTree G e0 phi2 Sgamma ∧
      TreeSequenceVertexSet Sgamma =
        (TreeSequenceVertexSet T \
          {C.blockVertex (D.gammaIndex d) 0,
            C.blockVertex (D.gammaIndex d) 1}) ∪ {R.u1} ∧
      TashkinovTree G e0 psi2 SgammaJ ∧
      TreeSequenceVertexSet SgammaJ =
        (TreeSequenceVertexSet T \
          {C.blockVertex R.blockIndex 0,
            C.blockVertex R.blockIndex 1}) ∪ {D.u0 d} ∧
      phi2 R.f1 = some d.1 ∧ psi2 (D.f0 d) = some d.1 := by
-- BODY
  sorry
