import Tablet.Degree
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.ScheideMaximalElementaryClosed

-- [TABLET NODE: ScheideMaximalOddOrder]
theorem ScheideMaximalOddOrder {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (htriple : KTriple G k e0 phi)
    (hmax : FixedPairMaximalTashkinovTree G e0 phi T) :
    Odd (TreeSequenceVertexSet T).card := by
-- BODY
  sorry
