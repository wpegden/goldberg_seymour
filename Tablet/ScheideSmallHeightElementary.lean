import Tablet.AdjacentEdges
import Tablet.BalancedGlobalMaximumTriple
import Tablet.ColoredVertexSetElementary
import Tablet.Critical
import Tablet.Elementary
import Tablet.FixedPairMaximalTashkinovTree
import Tablet.GlobalMaximumTriple
import Tablet.GlobalMaximumTripleExists
import Tablet.Incident
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.MaximumDegree
import Tablet.MissingColors
import Tablet.NormalGlobalMaximumTriple
import Tablet.PresentColors
import Tablet.ScheideBalancedExists
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideGraphHeight
import Tablet.ScheideGraphHeightOdd
import Tablet.ScheideKempePathHeightBound
import Tablet.ScheideLargeHeightElementary
import Tablet.ScheideMaximalKempePath
import Tablet.ScheideTrunkRotationPreserves
import Tablet.TashkinovOrder
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TrunkRotation
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ScheideSmallHeightElementary]
theorem ScheideSmallHeightElementary {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ)
    (hcritical : Critical G) (hindex : ChromaticIndex G = k + 1)
    (hdegree : MaximumDegree G + 1 ≤ k)
    (hnoisolated : ∀ v : V, ∃ e : E, Incident G v e)
    (hsmall : ScheideGraphHeight G < 5) :
    Elementary G := by
-- BODY
  sorry
