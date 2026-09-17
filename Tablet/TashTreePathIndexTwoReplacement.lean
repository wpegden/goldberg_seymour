import Tablet.ColoredVertexSetElementary
import Tablet.TashTreeBadPair
import Tablet.TashTreeMinimumBadPair
import Tablet.TashTreePathIndex
import Tablet.TashTreeRankLess
import Tablet.TashTreeSuffixPath
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: TashTreePathIndexTwoReplacement]
theorem TashTreePathIndexTwoReplacement {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hlen : 2 ≤ T.length) (hq : TashTreePathIndex G T = 2) :
    ∃ S : TreeSequence G e0,
      (∃ hST : S.length = T.length,
        (∀ r : Fin S.length,
          S.edge r = T.edge (Fin.cast hST r)) ∧
        S.vertex ⟨0, Nat.zero_lt_succ S.length⟩ =
          T.vertex ⟨1, by omega⟩ ∧
        S.vertex ⟨1, by omega⟩ =
          T.vertex ⟨0, Nat.zero_lt_succ T.length⟩ ∧
        (∀ r : Fin (S.length + 1), 2 ≤ r.val →
          S.vertex r = T.vertex
            (Fin.cast (congrArg (fun n => n + 1) hST) r))) ∧
      TashTreeBadPair G k e0 phi S ∧
      TashTreeRankLess G S T := by
-- BODY
  sorry
