import Tablet.AdjacentEdges
import Tablet.GlobalMaximumTriple
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.MissingColors
import Tablet.NormalGlobalMaximumTriple
import Tablet.PresentColors
import Tablet.ScheideGraphHeight
import Tablet.ScheideNormalisation
import Tablet.TreeSequence
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ScheideGraphHeightOdd]
theorem ScheideGraphHeightOdd {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T) :
    3 ≤ ScheideGraphHeight G ∧ Odd (ScheideGraphHeight G) := by
-- BODY
  sorry
