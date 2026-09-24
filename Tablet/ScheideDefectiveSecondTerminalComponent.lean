import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.ColoredVertexSetClosed
import Tablet.DefectiveColors
import Tablet.GlobalMaximumTriple
import Tablet.KTriple
import Tablet.MissingColors
import Tablet.OutsideTreeColorSwap
import Tablet.OutsideTreeColorSwapStable
import Tablet.PresentColors
import Tablet.ScheideDefectiveReturnData
import Tablet.ScheideDefectiveChainPath
import Tablet.ScheideDefectiveSetup
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideReducedConfiguration
import Tablet.StableColoring
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ScheideDefectiveSecondTerminalComponent]
theorem ScheideDefectiveSecondTerminalComponent {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideDefectiveReturnData G k e0 phi T C D d) :
    let gamma := C.gamma (D.gammaIndex d)
    let gammaJ := C.gamma R.blockIndex
    let psi1 := OutsideTreeColorSwap T phi gamma gammaJ
    let K := TwoColorComponent G psi1 gammaJ d.1 (Sum.inl R.v1)
    let psi2 := TwoColorComponentSwap G psi1 gammaJ d.1 (Sum.inl R.v1)
    IsProperEdgeColoring G psi1 ∧ IsOneEdgeUncolored psi1 e0 ∧
      StableColoring T ∅ phi psi1 ∧
      (∀ f : E, TreeIncidentEdge T f → psi1 f = phi f) ∧
      {q | ∃ r : Fin ((D.replacementPath d).length + 1),
        R.pathIndex.val ≤ r.val ∧
          (D.replacementPath d).getVert r.val = q} = K ∧
      Sum.inr R.f1 ∈ K ∧
      (∀ v : V, v ∈ TreeSequenceVertexSet T →
        (Sum.inl v ∈ K ↔ v = R.v1)) ∧
      (∀ q : Fin T.length, Sum.inr (T.edge q) ∉ K) ∧
      psi1 R.f1 = some d.1 ∧
      IsProperEdgeColoring G psi2 ∧ IsOneEdgeUncolored psi2 e0 ∧
      d.1 ∈ MissingColors G psi2 R.v1 ∧
      (∀ v ∈ TreeSequenceVertexSet T, v ≠ R.v1 →
        MissingColors G psi2 v = MissingColors G phi v) ∧
      psi2 (D.f0 d) = some d.1 := by
-- BODY
  sorry
