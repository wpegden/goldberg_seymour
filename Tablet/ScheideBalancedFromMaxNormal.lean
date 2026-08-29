import Tablet.BalancedGlobalMaximumTriple
import Tablet.AdjacentEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetElementary
import Tablet.FixedPairMaximalTashkinovTree
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.NormalGlobalMaximumTriple
import Tablet.NormalTripleTrunk
import Tablet.PresentColors
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideGraphHeightOdd
import Tablet.ScheideMaximalContainsEveryTree
import Tablet.TashTree
import Tablet.TashkinovOrder
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TreeUsedColors

-- [TABLET NODE: ScheideBalancedFromMaxNormal]
theorem ScheideBalancedFromMaxNormal {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hheight : N.height = ScheideGraphHeight G) :
    ∃ (T' : TreeSequence G e0)
      (N' : NormalGlobalMaximumTriple G k e0 phi T'),
      BalancedGlobalMaximumTriple N' ∧
        TreeSequenceVertexSet T' = TreeSequenceVertexSet T ∧
        TreeUsedColors phi T' ⊆ TreeUsedColors phi T := by
-- BODY
  sorry
