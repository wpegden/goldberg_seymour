import Tablet.ParallelExtensionColor
import Tablet.StableColoring
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeExit
import Tablet.TreeExitPath
import Tablet.TreeMissingColors
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.sc2

-- [TABLET NODE: HkuUnsupportedVertexColors]
theorem HkuUnsupportedVertexColors {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input) (q p : Fin rounds)
    (v : V) (hpq : p.val ≤ q.val)
    (hv : v ∈ TreeSequenceVertexSet (series.data.tree p.succ.castSucc))
    (hunused : ∀ j : Fin rounds, p.val ≤ j.val → j.val ≤ q.val →
      ¬ (series.data.kind j.succ = some TashkinovExtensionKind.PE ∧
        series.data.chosenVertex j.succ = some v)) :
    MissingColors G (series.data.coloring p.castSucc) v =
      MissingColors G (series.data.coloring q.succ) v := by
-- BODY
  sorry
