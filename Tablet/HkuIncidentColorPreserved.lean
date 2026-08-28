import Tablet.HkuMissingStoredMonotone
import Tablet.IsProperEdgeColoring
import Tablet.ParallelExtensionColor
import Tablet.StableColoring
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeExit
import Tablet.TreeExitPath
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.sc2

-- [TABLET NODE: HkuIncidentColorPreserved]
theorem HkuIncidentColorPreserved {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input) (q : Fin rounds)
    (f : E) (c : Fin k)
    (hf : TreeIncidentEdge (series.data.tree q.succ.castSucc) f)
    (hfc : series.data.coloring q.castSucc f = some c)
    (hc : c ∈ TreeMissingColors (series.data.coloring q.castSucc)
          (series.data.tree q.succ.castSucc) ∪
        TashkinovStoredColors series.data q.castSucc) :
    (series.data.coloring q.succ f = series.data.coloring q.castSucc f ∨
      (series.data.kind q.succ = some TashkinovExtensionKind.PE ∧
        series.data.connectingEdges q.succ = {f} ∧
        series.data.delta q.succ = some c ∧
        ∃ gamma : Fin k, series.data.gamma q.succ = some gamma ∧
          series.data.coloring q.succ f = some gamma)) ∧
    ∃ d : Fin k, series.data.coloring q.succ f = some d ∧
      d ∈ TreeMissingColors (series.data.coloring q.succ)
            (series.data.tree q.succ.castSucc) ∪
          TashkinovStoredColors series.data q.succ := by
-- BODY
  sorry
