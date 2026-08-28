import Tablet.OutsideTreeColorSwap
import Tablet.ScheideDefectiveChainBoundaryEdges
import Tablet.ScheideDefectiveChainLastReturnNoFree
import Tablet.ScheideExitVertexTreeExit
import Tablet.ScheideExitVertices

-- [TABLET NODE: ScheideExitNoFree]
theorem ScheideExitNoFree {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T) :
    ∀ v ∈ ScheideExitVertices T phi,
      Disjoint (MissingColors G phi v) (TreeFreeColors phi T) := by
-- BODY
  sorry
