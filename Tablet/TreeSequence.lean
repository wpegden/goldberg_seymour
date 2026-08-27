import Tablet.LooplessMultigraph

open scoped Sym2

-- [TABLET NODE: TreeSequence]
structure TreeSequence {V E : Type*} (G : LooplessMultigraph V E) (e0 : E) where
-- BODY
  length : ℕ
  positive : 1 ≤ length
  vertex : Fin (length + 1) → V
  edge : Fin length → E
  vertex_injective : Function.Injective vertex
  edge_injective : Function.Injective edge
  first_edge : edge ⟨0, positive⟩ = e0
  attaches : ∀ j : Fin length, ∃ i : Fin (j.val + 1),
    G.ends (edge j) =
      s(vertex j.succ,
        vertex (Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt))))
