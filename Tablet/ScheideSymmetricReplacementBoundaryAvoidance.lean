import Tablet.ScheideDefectiveChainBoundaryEdges
import Tablet.ScheideDefectiveChainPath
import Tablet.ScheideDefectiveSetup
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideReplacementInternalMissing
import Tablet.ScheideReplacementPairFixed
import Tablet.ScheideSymmetricReplacementBoundaryConfiguration
import Tablet.ScheideSymmetricReplacementPathOrder

-- [TABLET NODE: ScheideSymmetricReplacementBoundaryAvoidance]
theorem ScheideSymmetricReplacementBoundaryAvoidance {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    let gamma := C.gamma (D.gammaIndex d)
    let phiD := TwoColorComponentSwap G phi gamma d.1 (Sum.inl (D.v0 d))
    let Z := TreeSequenceVertexSet T \
      {C.blockVertex (D.gammaIndex d) 0,
        C.blockVertex (D.gammaIndex d) 1}
    ∀ (beta : Fin k) (v z : V)
      (p : (TwoColorIncidenceGraph G phiD gamma beta).Walk
        (Sum.inl v) (Sum.inl z)),
      v ∈ Z → beta ∈ MissingColors G phiD v →
      beta ∈ MissingColors G phi v →
      beta ∈ TreeFreeColors phiD R.replacementTree →
      beta ≠ d.1 → beta ≠ gamma →
      ScheideDefectiveChainPath R.replacementTree phiD gamma beta v z p →
      (Sum.inl R.u1 ∉ p.support ∧ Sum.inl R.u2 ∉ p.support) ∧
      (∀ f : E,
        f ∈ BoundaryColorEdges G phiD
            (TreeSequenceVertexSet R.replacementTree) gamma →
          ¬ Incident G R.u1 f ∧ ¬ Incident G R.u2 f) ∧
      ∀ f : E, phiD f = some gamma →
        (Incident G R.u1 f ∨ Incident G R.u2 f) →
        ∀ w ∈ Z, ¬ Incident G w f := by
-- BODY
  sorry
