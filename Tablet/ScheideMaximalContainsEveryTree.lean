import Tablet.ScheideMaximalElementaryClosed

-- [TABLET NODE: ScheideMaximalContainsEveryTree]
theorem ScheideMaximalContainsEveryTree {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T S : TreeSequence G e0)
    (htriple : KTriple G k e0 phi)
    (hmax : FixedPairMaximalTashkinovTree G e0 phi T)
    (hS : TashkinovTree G e0 phi S) :
    TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet T := by
-- BODY
  sorry
