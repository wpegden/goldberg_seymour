import Tablet.ParallelExtensionColor
import Tablet.StableColoring
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeExit
import Tablet.TreeExitPath
import Tablet.TreeMissingColors
import Tablet.TreeSequenceInitialSegment
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceDegreeAtMostTwo

-- [TABLET NODE: HkuMissingStoredMonotone]
theorem HkuMissingStoredMonotone {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input) (q : Fin rounds) :
    TreeMissingColors (series.data.coloring q.castSucc)
          (series.data.tree q.succ.castSucc) ∪
        TashkinovStoredColors series.data q.castSucc ⊆
      TreeMissingColors (series.data.coloring q.succ)
          (series.data.tree q.succ.castSucc) ∪
        TashkinovStoredColors series.data q.succ ∧
    TreeMissingColors (series.data.coloring q.succ)
          (series.data.tree q.succ.castSucc) ∪
        TashkinovStoredColors series.data q.succ ⊆
      TreeMissingColors (series.data.coloring q.succ)
          (series.data.tree q.succ.succ) ∪
        TashkinovStoredColors series.data q.succ := by
-- BODY
  sorry
