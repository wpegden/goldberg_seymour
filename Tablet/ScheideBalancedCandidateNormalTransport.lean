import Tablet.GlobalMaximumTriple
import Tablet.NormalGlobalMaximumTriple
import Tablet.NormalTripleTrunk
import Tablet.ScheideBalancedCandidate
import Tablet.TashkinovOrder
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: ScheideBalancedCandidateNormalTransport]
theorem ScheideBalancedCandidateNormalTransport {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T S : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hS : ScheideBalancedCandidate N S)
    (hvertices : TreeSequenceVertexSet S = TreeSequenceVertexSet T) :
    ∃ N' : NormalGlobalMaximumTriple G k e0 phi S,
      N'.height = N.height := by
-- BODY
  sorry
