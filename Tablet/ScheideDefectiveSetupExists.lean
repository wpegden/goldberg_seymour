import Tablet.ScheideDefectiveSetup
import Tablet.ScheideGlobalMaximumMissingCounts
import Tablet.ScheideStructuralExitsInBase
import Tablet.ScheideGlobalMaximumBoundaryFacts
import Tablet.ScheideGlobalMaximumOrder
import Tablet.TwoColorComponentSpanningPath

-- [TABLET NODE: ScheideDefectiveSetupExists]
theorem ScheideDefectiveSetupExists {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (hdef : DefectiveColors G phi (TreeSequenceVertexSet T) ≠ ∅) :
    Nonempty (ScheideDefectiveSetup G k e0 phi T C) := by
-- BODY
  sorry
