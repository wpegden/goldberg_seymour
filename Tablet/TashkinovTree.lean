import Tablet.MissingColors
import Tablet.TreeSequence

-- [TABLET NODE: TashkinovTree]
def TashkinovTree {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) {k : ℕ} (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) : Prop :=
-- BODY
  ∀ j : Fin T.length, 1 ≤ j.val →
    ∃ i : Fin (j.val + 1), ∃ c : Fin k,
      phi (T.edge j) = some c ∧
        c ∈ MissingColors G phi
          (T.vertex (Fin.castLT i
            (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt))))
