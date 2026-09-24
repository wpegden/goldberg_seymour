import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ScheideDefectiveChainBoundaryEdges
import Tablet.ScheideDefectiveChainPath
import Tablet.ScheideDefectiveSetup
import Tablet.ScheideExitVertex
import Tablet.ScheideExitVertices
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideReducedConfiguration
import Tablet.ScheideReplacementData
import Tablet.ScheideReplacementInternalMissing
import Tablet.ScheideStructuralExitsInBase
import Tablet.ScheideSymmetricOriginalFreePath
import Tablet.TwoColorIncidenceDegreeAtMostTwo

-- [TABLET NODE: ScheideSymmetricOriginalPathOrder]
theorem ScheideSymmetricOriginalPathOrder {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    ∀ (beta : Fin k) (v z : V)
      (p : (TwoColorIncidenceGraph G phi d.1 beta).Walk
        (Sum.inl v) (Sum.inl z)),
      v ∈ TreeSequenceVertexSet T \
          {C.blockVertex (D.gammaIndex d) 0,
            C.blockVertex (D.gammaIndex d) 1} →
      beta ∈ MissingColors G phi v →
      beta ∈ TreeFreeColors phi T →
      beta ≠ C.gamma (D.gammaIndex d) →
      ScheideDefectiveChainPath T phi d.1 beta v z p →
      ∃ (h : E) (i0 i1 i2 i3 i4 qv qf : Fin (p.length + 1)),
        phi h = some beta ∧ G.ends h = s(R.u1, R.u2) ∧
        i1.val = i0.val + 1 ∧ i2.val = i1.val + 1 ∧
        i3.val = i2.val + 1 ∧ i4.val = i3.val + 1 ∧
        ((p.getVert i0.val = Sum.inr R.f1 ∧
            p.getVert i1.val = Sum.inl R.u1 ∧
            p.getVert i2.val = Sum.inr h ∧
            p.getVert i3.val = Sum.inl R.u2 ∧
            p.getVert i4.val = Sum.inr R.f2) ∨
          (p.getVert i0.val = Sum.inr R.f2 ∧
            p.getVert i1.val = Sum.inl R.u2 ∧
            p.getVert i2.val = Sum.inr h ∧
            p.getVert i3.val = Sum.inl R.u1 ∧
            p.getVert i4.val = Sum.inr R.f1)) ∧
        i4.val < qv.val ∧ qf.val = qv.val + 1 ∧
        p.getVert qv.val = Sum.inl (D.v0 d) ∧
        p.getVert qf.val = Sum.inr (D.f0 d) ∧
        ∀ r : Fin (p.length + 1), qv.val < r.val →
          ∀ w : V, p.getVert r.val = Sum.inl w →
            w ∉ TreeSequenceVertexSet T := by
-- BODY
  sorry
