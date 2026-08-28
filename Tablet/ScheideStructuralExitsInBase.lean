import Tablet.ScheideExitNoFree
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideGlobalMaximumUnused
import Tablet.ScheideReducedConfiguration
import Tablet.GlobalMaximumTriple
import Tablet.MaximumDegree
import Tablet.MissingColors

-- [TABLET NODE: ScheideStructuralExitsInBase]
theorem ScheideStructuralExitsInBase {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T) :
    ScheideExitVertices T phi ⊆ Finset.univ.image C.y := by
-- BODY
  sorry
