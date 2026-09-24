import Tablet.Incident
import Tablet.ScheideReducedConfiguration
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: ScheideSelectedBlockDeletion]
theorem ScheideSelectedBlockDeletion {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T) (i : Fin C.s) :
    ∃ S : TreeSequence G e0,
      TreeSequenceVertexSet S = TreeSequenceVertexSet T \
        {C.blockVertex i 0, C.blockVertex i 1} ∧
      S.length + 2 = T.length ∧
      (∃ rV : Fin (S.length + 1) → Fin (T.length + 1),
        (∀ q : Fin (S.length + 1), S.vertex q = T.vertex (rV q)) ∧
        (∀ q : Fin (S.length + 1), q.val < C.p + 2 * i.val →
          (rV q).val = q.val) ∧
        ∀ q : Fin (S.length + 1), C.p + 2 * i.val ≤ q.val →
          (rV q).val = q.val + 2) ∧
      (∃ rE : Fin S.length → Fin T.length,
        (∀ q : Fin S.length, S.edge q = T.edge (rE q)) ∧
        (∀ q : Fin S.length, q.val < C.p - 1 + 2 * i.val →
          (rE q).val = q.val) ∧
        ∀ q : Fin S.length, C.p - 1 + 2 * i.val ≤ q.val →
          (rE q).val = q.val + 2) ∧
      (∀ a : Fin C.p, ∃ q : Fin (S.length + 1),
        q.val = a.val ∧ S.vertex q = C.y a) ∧
      (∀ a : Fin (C.p - 1), ∃ q : Fin S.length,
        q.val = a.val ∧ S.edge q = C.baseEdge a) ∧
      (∀ r : Fin C.s, r ≠ i → ∀ j : Fin 2,
        ∃ qv : Fin (S.length + 1), ∃ qe : Fin S.length,
          C.p ≤ qv.val ∧ C.p - 1 ≤ qe.val ∧
          qe.val + 1 = qv.val ∧
          S.vertex qv = C.blockVertex r j ∧
          S.edge qe = C.blockEdge r j) ∧
      (∀ q : Fin S.length,
        (∃ a : Fin (C.p - 1), q.val = a.val ∧ S.edge q = C.baseEdge a) ∨
        (∃ r : Fin C.s, ∃ j : Fin 2, r ≠ i ∧
          C.p - 1 ≤ q.val ∧ S.edge q = C.blockEdge r j)) ∧
      (∀ q : Fin S.length, ∃ r : Fin T.length, S.edge q = T.edge r) ∧
      ∀ q : Fin S.length,
        ¬ Incident G (C.blockVertex i 0) (S.edge q) ∧
        ¬ Incident G (C.blockVertex i 1) (S.edge q) := by
-- BODY
  sorry
