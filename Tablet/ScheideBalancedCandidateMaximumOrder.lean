import Tablet.AdjacentEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetElementary
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.NormalGlobalMaximumTriple
import Tablet.PresentColors
import Tablet.ScheideBalancedCandidate
import Tablet.TashTree
import Tablet.TashkinovOrder
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TreeUsedColors

-- [TABLET NODE: ScheideBalancedCandidateMaximumOrder]
theorem ScheideBalancedCandidateMaximumOrder {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T S : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hS : ScheideBalancedCandidate N S)
    (hmax : ∀ R : TreeSequence G e0, ScheideBalancedCandidate N R →
      (TreeSequenceVertexSet R).card ≤
        (TreeSequenceVertexSet S).card) :
    (TreeSequenceVertexSet S).card = TashkinovOrder G := by
-- BODY
  sorry
