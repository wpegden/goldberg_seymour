import Tablet.ChromaticIndexSpec
import Tablet.Critical
import Tablet.DeleteEdge
import Tablet.GlobalMaximumTriple
import Tablet.HasKEdgeColoring
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.MaximumDegree
import Tablet.TashkinovOrder
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: GlobalMaximumTripleExists]
theorem GlobalMaximumTripleExists {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ)
    (hcritical : Critical G) (hindex : ChromaticIndex G = k + 1)
    (hdegree : MaximumDegree G + 1 ≤ k) :
    ∃ (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0),
      GlobalMaximumTriple G k e0 phi T := by
-- BODY
  sorry
