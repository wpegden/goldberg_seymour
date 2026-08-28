import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
import Tablet.GlobalMaximumTriple
import Tablet.MissingColors
import Tablet.TwoColorIncidenceGraph

open scoped Sym2

-- [TABLET NODE: NormalGlobalMaximumTriple]
structure NormalGlobalMaximumTriple {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) where
-- BODY
  global : GlobalMaximumTriple G k e0 phi T
  height : ℕ
  height_lower : 2 ≤ height
  height_upper : height ≤ T.length + 1
  alpha : Fin k
  beta : Fin k
  alpha_missing : alpha ∈ MissingColors G phi
    (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩)
  beta_missing : beta ∈ MissingColors G phi
    (T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩)
  closingEdge : E
  lastIndex : Fin (T.length + 1)
  lastIndex_height : lastIndex.val + 1 = height
  closing_ends : G.ends closingEdge =
    s(T.vertex lastIndex, T.vertex ⟨0, Nat.zero_lt_succ T.length⟩)
  closingPath : (TwoColorIncidenceGraph G phi alpha beta).Walk
    (Sum.inl (T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩))
    (Sum.inl (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩))
  closingPath_isPath : closingPath.IsPath
  closingPath_length : closingPath.length = 2 * (height - 1)
  closingPath_vertices : ∀ v : V,
    Sum.inl v ∈ closingPath.support ↔
      ∃ i : Fin height,
        v = T.vertex (Fin.castLE height_upper i)
  closingPath_edges : ∀ f : E,
    Sum.inr f ∈ closingPath.support ↔
      f = closingEdge ∨
        ∃ j : Fin T.length,
          1 ≤ j.val ∧ j.val + 2 ≤ height ∧ f = T.edge j
  trunk_edge_ends : ∀ j : Fin T.length,
    1 ≤ j.val → j.val + 2 ≤ height →
      G.ends (T.edge j) =
        s(T.vertex ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩, T.vertex j.succ)
