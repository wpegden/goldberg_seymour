import Tablet.TashTreeBadPair
import Tablet.TashTreeRankLess

-- [TABLET NODE: TashTreeMinimumBadPair]
def TashTreeMinimumBadPair {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) : Prop :=
-- BODY
  TashTreeBadPair G k e0 phi T ∧
    ∀ {psi : PartialEdgeColoring E k} {S : TreeSequence G e0},
      TashTreeBadPair G k e0 psi S → ¬ TashTreeRankLess G S T
