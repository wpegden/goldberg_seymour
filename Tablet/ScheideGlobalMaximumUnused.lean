import Tablet.DefectiveColors
import Tablet.GlobalMaximumTriple
import Tablet.ScheideGlobalMaximumOrder
import Tablet.TreeFreeColors

-- [TABLET NODE: ScheideGlobalMaximumUnused]
theorem ScheideGlobalMaximumUnused {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T) :
    Disjoint (DefectiveColors G phi (TreeSequenceVertexSet T))
        (TreeUsedColors phi T) ∧
      Disjoint (TreeFreeColors phi T) (TreeUsedColors phi T) := by
-- BODY
  sorry
