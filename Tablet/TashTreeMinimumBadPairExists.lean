import Tablet.TashTreeBadPair
import Tablet.TashTreeMinimumBadPair
import Tablet.TashTreePathIndex
import Tablet.TashTreeRankLess

-- [TABLET NODE: TashTreeMinimumBadPairExists]
theorem TashTreeMinimumBadPairExists {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (htriple : KTriple G k e0 phi) (hT : TashkinovTree G e0 phi T)
    (hbad : ¬ ColoredVertexSetElementary G phi (TreeSequenceVertexSet T)) :
    ∃ psi : PartialEdgeColoring E k, ∃ S : TreeSequence G e0,
      TashTreeMinimumBadPair G k e0 psi S := by
-- BODY
  sorry
