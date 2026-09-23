import Tablet.MissingColors
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TwoColorIncidenceGraph

open scoped Sym2

-- [TABLET NODE: ScheideReversedPathCertificate]
structure ScheideReversedPathCertificate {V E : Type*}
    [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (alpha beta : Fin k)
    (p : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩))
      (Sum.inl (T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩))) where
-- BODY
  tree : TreeSequence G e0
  closingEdge : E
  length_lower : 2 ≤ tree.length
  length_eq : tree.length = p.length / 2
  tashkinov : TashkinovTree G e0 phi tree
  first_vertex : tree.vertex ⟨0, Nat.zero_lt_succ tree.length⟩ =
    T.vertex ⟨0, Nat.zero_lt_succ T.length⟩
  second_vertex : tree.vertex ⟨1, Nat.succ_lt_succ tree.positive⟩ =
    T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩
  closing_ends : G.ends closingEdge =
    s(tree.vertex (Fin.last tree.length),
      tree.vertex ⟨0, Nat.zero_lt_succ tree.length⟩)
  path_vertices : ∀ v : V, Sum.inl v ∈ p.support ↔
    ∃ i : Fin (tree.length + 1), v = tree.vertex i
  path_edges : ∀ f : E, Sum.inr f ∈ p.support ↔
    f = closingEdge ∨
      ∃ j : Fin tree.length, 1 ≤ j.val ∧ f = tree.edge j
  trunk_edge_ends : ∀ j : Fin tree.length, 1 ≤ j.val →
    G.ends (tree.edge j) =
      s(tree.vertex ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩, tree.vertex j.succ)
