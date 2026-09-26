import Tablet.BoundaryEdges
import Tablet.GlobalMaximumTriple
import Tablet.KTriple
import Tablet.MissingColors
import Tablet.ScheideDefectiveSetup
import Tablet.ScheideReducedConfiguration
import Tablet.ScheideReplacementData
import Tablet.ScheideStructuralConfiguration
import Tablet.TashkinovOrder
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceBoundaryEdgeAppendExists
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceGraph

open scoped Sym2

-- [TABLET NODE: ScheideEnlargedStrictAugmentation]
theorem ScheideEnlargedStrictAugmentation {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R : ∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d) :
    (∃ (alpha : Fin k)
      (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
      (f : E) (w u : V),
      let phiD := TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) d.1 (Sum.inl (D.v0 d))
      let Q := TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u)
      let psi := TwoColorComponentSwap G phiD D.alpha0 alpha (Sum.inl u)
      alpha ≠ D.alpha0 ∧
        G.ends f = s(w, u) ∧
        phiD f = some alpha ∧
        Sum.inr f ∈ Q ∧
        (∀ v ∈ TreeSequenceVertexSet T, Sum.inl v ∉ Q) ∧
        GlobalMaximumTriple G k e0 psi (R d).replacementTree ∧
        D.alpha0 ∈ MissingColors G phiD
          (C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩) ∧
        C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ ∈
          TreeSequenceVertexSet (R d).replacementTree ∧
        w ∈ TreeSequenceVertexSet (R d).replacementTree ∧
        u ∉ TreeSequenceVertexSet (R d).replacementTree ∧
        f ∉ Finset.univ.image (R d).replacementTree.edge) →
    ∃ (psi : PartialEdgeColoring E k) (S : TreeSequence G e0),
      KTriple G k e0 psi ∧
        TashkinovTree G e0 psi S ∧
        (TreeSequenceVertexSet S).card = TashkinovOrder G + 1 := by
-- BODY
  sorry
