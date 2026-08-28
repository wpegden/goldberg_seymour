import Tablet.GlobalMaximumTriple
import Tablet.ScheideMaximalElementaryClosed
import Tablet.ScheideMaximalOddOrder

-- [TABLET NODE: ScheideGlobalMaximumOrder]
theorem ScheideGlobalMaximumOrder {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T) :
    TashkinovOrder G = (TreeSequenceVertexSet T).card ∧
      3 ≤ (TreeSequenceVertexSet T).card ∧
      Odd (TreeSequenceVertexSet T).card ∧
      ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) ∧
      ColoredVertexSetClosed G phi (TreeSequenceVertexSet T) := by
-- BODY
  sorry
