import Tablet.ColoredVertexSetElementary
import Tablet.GlobalMaximumTriple
import Tablet.KTriple
import Tablet.MissingColors
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideReducedConfiguration
import Tablet.ScheideStructuralConfiguration
import Tablet.ScheideStructuralReorderingData
import Tablet.ScheideStructuralSelectionData
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: ScheideStructuralReducedAssembly]
theorem ScheideStructuralReducedAssembly {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideStructuralConfiguration G k e0 phi T)
    (D : ScheideStructuralSelectionData G k e0 phi T C)
    (T' : TreeSequence G e0)
    (Q : ScheideStructuralReorderingData G k e0 phi T C D T') :
    ∃ R : ScheideReducedConfiguration G k e0 phi T',
      TreeSequenceVertexSet T' = TreeSequenceVertexSet T ∧
      (∀ q : Fin C.p, C.y q ∈ Finset.univ.image R.y) ∧
      (∀ i : Fin C.s,
        (∃ r : Fin R.s, C.gamma i = R.gamma r ∧
          ∀ j : Fin 2, C.blockVertex i j = R.blockVertex r j ∧
            C.blockEdge i j = R.blockEdge r j) ∨
        ∀ j : Fin 2, C.blockVertex i j ∈ Finset.univ.image R.y) := by
-- BODY
  sorry
