import Tablet.BalancedGlobalMaximumTriple
import Tablet.DefectiveColors
import Tablet.Elementary
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.KTriple
import Tablet.NormalGlobalMaximumTriple
import Tablet.ScheideDefectiveChainDepartureReturn
import Tablet.ScheideDefectiveChainPathExists
import Tablet.ScheideDepartureReturn
import Tablet.ScheideExitNoFree
import Tablet.ScheideExitVertex
import Tablet.ScheideExitVertices
import Tablet.ScheideGlobalMaximumBoundaryFacts
import Tablet.ScheideGlobalMaximumMissingCounts
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideGraphHeight
import Tablet.TashkinovOrder
import Tablet.TreeFreeColors
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TreeUsedColors
import Tablet.egraph2

-- [TABLET NODE: ScheideLargeHeightFullTrunk]
theorem ScheideLargeHeightFullTrunk {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hbalanced : BalancedGlobalMaximumTriple N)
    (hnoisolated : ∀ v : V, ∃ e : E, Incident G v e)
    (hheight : ScheideGraphHeight G = TashkinovOrder G) :
    Elementary G := by
-- BODY
  sorry
