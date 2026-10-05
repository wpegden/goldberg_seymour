import Tablet.BoundaryColorEdges
import Tablet.TashkinovAugmentation
import Tablet.TreeMissingColors
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: BoundaryMissingColorAugmentation]
theorem BoundaryMissingColorAugmentation {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (X : TreeSequence G e0)
    (c : Fin k) (f : E)
    (hf : f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet X) c)
    (hc : c ∈ TreeMissingColors phi X) :
    ∃ Xplus : TreeSequence G e0,
      TreeSequenceAdjoinEdge X f Xplus ∧
      TashkinovAugmentation phi X Xplus ∧
      TreeSequenceVertexSet X ⊂ TreeSequenceVertexSet Xplus := by
-- BODY
  sorry
