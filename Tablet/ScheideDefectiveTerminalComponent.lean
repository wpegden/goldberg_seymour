import Tablet.DefectiveColors
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.OutsideTreeColorSwap
import Tablet.OutsideTreeColorSwapStable
import Tablet.ScheideDefectiveChainPath
import Tablet.ScheideDefectiveSetup
import Tablet.ScheideGlobalMaximumOrder
import Tablet.StableColoring
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ScheideDefectiveTerminalComponent]
theorem ScheideDefectiveTerminalComponent {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)}) :
    let gamma := C.gamma (D.gammaIndex d)
    let phi1 := OutsideTreeColorSwap T phi D.alpha0 gamma
    let K := TwoColorComponent G phi1 gamma d.1 (Sum.inl (D.v0 d))
    IsProperEdgeColoring G phi1 ∧ IsOneEdgeUncolored phi1 e0 ∧
      StableColoring T ∅ phi phi1 ∧
      (∀ f : E, TreeIncidentEdge T f → phi1 f = phi f) ∧
      {q | ∃ r : Fin ((D.initialPath d).length + 1),
        (D.v0Index d).val ≤ r.val ∧ (D.initialPath d).getVert r.val = q} = K ∧
      Sum.inr (D.f0 d) ∈ K ∧
      (∀ v : V, v ∈ TreeSequenceVertexSet T →
        (Sum.inl v ∈ K ↔ v = D.v0 d)) ∧
      (∀ q : Fin T.length, Sum.inr (T.edge q) ∉ K) ∧
      ∀ f : E, Sum.inr f ∈ K →
        phi1 f = some gamma ∨ phi1 f = some d.1 := by
-- BODY
  sorry
