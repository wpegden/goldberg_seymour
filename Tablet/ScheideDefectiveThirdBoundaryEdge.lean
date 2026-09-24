import Tablet.AdjacentEdges
import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.DefectiveColors
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.InternalEdges
import Tablet.IsProperEdgeColoring
import Tablet.IsOneEdgeUncolored
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.OutsideTreeColorSwap
import Tablet.PresentColors
import Tablet.ScheideDefectiveDeletedTreePair
import Tablet.ScheideDefectiveNoCross
import Tablet.ScheideDefectiveReturnData
import Tablet.ScheideDefectiveSecondTerminalComponent
import Tablet.ScheideDefectiveTerminalComponent
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideReducedConfiguration
import Tablet.ScheideStructuralInternalPair
import Tablet.ScheideStructuralExitsInBase
import Tablet.TashkinovOrder
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceBoundaryEdgeAppendExists
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponentSwap

open scoped Sym2

-- [TABLET NODE: ScheideDefectiveThirdBoundaryEdge]
theorem ScheideDefectiveThirdBoundaryEdge {V E : Type*}
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
    let Z := TreeSequenceVertexSet T \
      ({C.blockVertex (D.gammaIndex d) 0,
          C.blockVertex (D.gammaIndex d) 1} ∪
        {C.blockVertex R.blockIndex 0,
          C.blockVertex R.blockIndex 1})
    ∃ f2 : E, ∃ z2 u2 : V,
      phi f2 = some d.1 ∧ G.ends f2 = s(z2, u2) ∧
      z2 ∈ Z ∧ u2 ∉ TreeSequenceVertexSet T ∧
      f2 ≠ D.f0 d ∧ f2 ≠ R.f1 ∧
      z2 ≠ D.v0 d ∧ z2 ≠ R.v1 ∧
      phi2 f2 = some d.1 ∧ psi2 f2 = some d.1 ∧
      u2 ≠ D.u0 d ∧ u2 ≠ R.u1 := by
-- BODY
  sorry
