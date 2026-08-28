import Tablet.ColoredVertexSetClosed
import Tablet.FixedPairMaximalTashkinovTree
import Tablet.KTriple
import Tablet.TashTree

-- [TABLET NODE: ScheideMaximalElementaryClosed]
theorem ScheideMaximalElementaryClosed {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (htriple : KTriple G k e0 phi)
    (hmax : FixedPairMaximalTashkinovTree G e0 phi T) :
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) ∧
      ColoredVertexSetClosed G phi (TreeSequenceVertexSet T) := by
-- BODY
  sorry
