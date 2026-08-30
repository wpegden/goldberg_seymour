import Tablet.ColoredVertexSetElementary
import Tablet.DefectiveColor
import Tablet.DefectiveColors
import Tablet.GlobalMaximumTriple
import Tablet.KTriple
import Tablet.MissingColors
import Tablet.ScheideDefectiveChainPath
import Tablet.ScheideExitVertex
import Tablet.ScheideExitVertices
import Tablet.ScheideReducedConfiguration
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideStructuralConfiguration
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: ScheideStructuralReduction]
theorem ScheideStructuralReduction {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideStructuralConfiguration G k e0 phi T) :
    ∃ (T' : TreeSequence G e0)
      (R : ScheideReducedConfiguration G k e0 phi T'),
      TreeSequenceVertexSet T' = TreeSequenceVertexSet T ∧
      (∀ q : Fin C.p, C.y q ∈ Finset.univ.image R.y) ∧
      (∀ i : Fin C.s,
        (∃ r : Fin R.s, C.gamma i = R.gamma r ∧
          ∀ j : Fin 2, C.blockVertex i j = R.blockVertex r j ∧
            C.blockEdge i j = R.blockEdge r j) ∨
        ∀ j : Fin 2, C.blockVertex i j ∈ Finset.univ.image R.y) := by
-- BODY
  sorry
