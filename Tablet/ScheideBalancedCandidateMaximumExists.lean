import Tablet.GlobalMaximumTriple
import Tablet.NormalGlobalMaximumTriple
import Tablet.NormalTripleTrunk
import Tablet.ScheideBalancedCandidate
import Tablet.ScheideGraphHeightOdd
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TreeUsedColors

-- [TABLET NODE: ScheideBalancedCandidateMaximumExists]
theorem ScheideBalancedCandidateMaximumExists {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hheight : N.height = ScheideGraphHeight G) :
    ∃ S : TreeSequence G e0,
      ScheideBalancedCandidate N S ∧
        ∀ R : TreeSequence G e0, ScheideBalancedCandidate N R →
          (TreeSequenceVertexSet R).card ≤
            (TreeSequenceVertexSet S).card := by
-- BODY
  sorry
