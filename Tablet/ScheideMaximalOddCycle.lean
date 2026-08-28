import Tablet.OddCycleIn
import Tablet.ScheideMaximalKempePath

-- [TABLET NODE: ScheideMaximalOddCycle]
theorem ScheideMaximalOddCycle {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (htriple : KTriple G k e0 phi)
    (hmax : FixedPairMaximalTashkinovTree G e0 phi T) :
    OddCycleIn G (TreeSequenceVertexSet T) := by
-- BODY
  sorry
