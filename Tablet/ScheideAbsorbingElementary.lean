import Tablet.AbsorbingVertices
import Tablet.ScheideGlobalMaximumFourFree
import Tablet.ScheideGlobalMaximumOrder
import Tablet.TwoColorComponentSpanningPath

-- [TABLET NODE: ScheideAbsorbingElementary]
theorem ScheideAbsorbingElementary {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T) :
    ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet T ∪ AbsorbingVertices T phi) := by
-- BODY
  sorry
