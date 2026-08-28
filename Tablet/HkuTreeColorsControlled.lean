import Tablet.HkuIncidentColorPreserved
import Tablet.IsOneEdgeUncolored
import Tablet.StableColoring
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeUsedColors

-- [TABLET NODE: HkuTreeColorsControlled]
theorem HkuTreeColorsControlled {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input) (q : Fin rounds) :
    TreeUsedColors (series.data.coloring q.castSucc)
          (series.data.tree q.succ.castSucc) ⊆
        TreeMissingColors (series.data.coloring q.castSucc)
            (series.data.tree q.succ.castSucc) ∪
          TashkinovStoredColors series.data q.castSucc ∧
    TreeUsedColors (series.data.coloring q.succ)
          (series.data.tree q.succ.castSucc) ⊆
        TreeMissingColors (series.data.coloring q.succ)
            (series.data.tree q.succ.castSucc) ∪
          TashkinovStoredColors series.data q.succ ∧
    ∀ sigma : PartialEdgeColoring E k,
      IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
      StableColoring (series.data.tree q.succ.castSucc)
        (TashkinovStoredColors series.data q.succ)
        (series.data.coloring q.succ) sigma →
      ∀ j : Fin (series.data.tree q.succ.castSucc).length,
        sigma ((series.data.tree q.succ.castSucc).edge j) =
          series.data.coloring q.succ
            ((series.data.tree q.succ.castSucc).edge j) := by
-- BODY
  sorry
