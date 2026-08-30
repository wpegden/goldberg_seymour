import Tablet.AdjacentEdges
import Tablet.BalancedGlobalMaximumTriple
import Tablet.ColoredVertexSetElementary
import Tablet.Elementary
import Tablet.FixedPairMaximalTashkinovTree
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.MissingColors
import Tablet.NormalGlobalMaximumTriple
import Tablet.ScheideExitNoFree
import Tablet.ScheideExitVertex
import Tablet.ScheideExitVertices
import Tablet.ScheideGlobalMaximumMissingCounts
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideGraphHeight
import Tablet.ScheideGraphHeightOdd
import Tablet.ScheideMaximalKempePath
import Tablet.ScheideStructuralConfiguration
import Tablet.ScheideStructuralLemma
import Tablet.TashkinovOrder
import Tablet.TashkinovTree
import Tablet.TreeFreeColors
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TreeUsedColors
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ScheideLargeHeightOneTailPair]
theorem ScheideLargeHeightOneTailPair {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hbalanced : BalancedGlobalMaximumTriple N)
    (hnoisolated : ∀ v : V, ∃ e : E, Incident G v e)
    (hheight : ScheideGraphHeight G + 2 = TashkinovOrder G) :
    Elementary G := by
-- BODY
  sorry
