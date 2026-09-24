import Tablet.ScheideExitNoFree
import Tablet.ScheideDefectiveChainBoundaryEdges
import Tablet.ScheideDefectiveSetup
import Tablet.ScheideDefectiveSwitchEffect
import Tablet.ScheideExitVertex
import Tablet.ScheideGlobalMaximumMissingCounts
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideGlobalMaximumUnused
import Tablet.ScheideReplacementData
import Tablet.ScheideReplacementPairFixed
import Tablet.ScheideStructuralInternalPair
import Tablet.ScheideStructuralConfiguration
import Tablet.ScheideStructuralExitsInBase
import Tablet.ScheideSymmetricReplacementBoundaryConfiguration
import Tablet.ScheideSymmetricReplacementFreePath
import Tablet.TwoColorIncidenceDegreeAtMostTwo

-- [TABLET NODE: ScheideSymmetricReplacementPathOrder]
theorem ScheideSymmetricReplacementPathOrder {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    let gamma := C.gamma (D.gammaIndex d)
    let phiD := TwoColorComponentSwap G phi gamma d.1 (Sum.inl (D.v0 d))
    ∀ (beta : Fin k) (v z : V)
      (p : (TwoColorIncidenceGraph G phiD gamma beta).Walk
        (Sum.inl v) (Sum.inl z)),
      v ∈ TreeSequenceVertexSet T \
          {C.blockVertex (D.gammaIndex d) 0,
            C.blockVertex (D.gammaIndex d) 1} →
      beta ∈ MissingColors G phiD v → beta ∈ MissingColors G phi v →
      beta ∈ TreeFreeColors phiD R.replacementTree →
      beta ≠ d.1 → beta ≠ gamma →
      ScheideDefectiveChainPath R.replacementTree phiD gamma beta v z p →
      ∃ (h : E) (i0 i1 i2 i3 i4 qv qf : Fin (p.length + 1)),
        phiD h = some beta ∧
        G.ends h = s(C.blockVertex (D.gammaIndex d) 0,
          C.blockVertex (D.gammaIndex d) 1) ∧
        i1.val = i0.val + 1 ∧ i2.val = i1.val + 1 ∧
        i3.val = i2.val + 1 ∧ i4.val = i3.val + 1 ∧
        ((p.getVert i0.val = Sum.inr (C.blockEdge (D.gammaIndex d) 0) ∧
            p.getVert i1.val = Sum.inl (C.blockVertex (D.gammaIndex d) 0) ∧
            p.getVert i2.val = Sum.inr h ∧
            p.getVert i3.val = Sum.inl (C.blockVertex (D.gammaIndex d) 1) ∧
            p.getVert i4.val = Sum.inr (C.blockEdge (D.gammaIndex d) 1)) ∨
          (p.getVert i0.val = Sum.inr (C.blockEdge (D.gammaIndex d) 1) ∧
            p.getVert i1.val = Sum.inl (C.blockVertex (D.gammaIndex d) 1) ∧
            p.getVert i2.val = Sum.inr h ∧
            p.getVert i3.val = Sum.inl (C.blockVertex (D.gammaIndex d) 0) ∧
            p.getVert i4.val = Sum.inr (C.blockEdge (D.gammaIndex d) 0))) ∧
        i4.val < qv.val ∧ qf.val = qv.val + 1 ∧
        p.getVert qv.val = Sum.inl (D.v0 d) ∧
        p.getVert qf.val = Sum.inr (D.f0 d) ∧
        (∀ r : Fin (p.length + 1), qv.val < r.val →
          ∀ w : V, p.getVert r.val = Sum.inl w →
            w ∉ TreeSequenceVertexSet R.replacementTree) ∧
        R.u1 ∉ ScheideExitVertices R.replacementTree phiD ∧
        R.u2 ∉ ScheideExitVertices R.replacementTree phiD := by
-- BODY
  sorry
