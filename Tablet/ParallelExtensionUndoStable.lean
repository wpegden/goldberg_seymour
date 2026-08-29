import Tablet.AdjacentEdges
import Tablet.DefectiveVertex
import Tablet.HkuMissingStoredMonotone
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDefectiveChoice
import Tablet.MissingColors
import Tablet.ParallelExtensionColor
import Tablet.PresentColors
import Tablet.StableColoring
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeIncidentEdge
import Tablet.TreeExit
import Tablet.TreeExitPath
import Tablet.TreeMissingColors
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.sc1
import Tablet.sc2

-- [TABLET NODE: ParallelExtensionUndoStable]
theorem ParallelExtensionUndoStable {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input) (q : Fin rounds)
    (v : V) (gamma delta : Fin k)
    (hkind : series.data.kind q.succ = some TashkinovExtensionKind.PE)
    (hvertex : series.data.chosenVertex q.succ = some v)
    (hgamma : series.data.gamma q.succ = some gamma)
    (hdelta : series.data.delta q.succ = some delta)
    (sigma : PartialEdgeColoring E k)
    (hsigmaProper : IsProperEdgeColoring G sigma)
    (hsigmaOneUncolored : IsOneEdgeUncolored sigma e0)
    (hsigmaStable : StableColoring (series.data.tree q.succ.castSucc)
      (TashkinovStoredColors series.data q.succ)
      (series.data.coloring q.succ) sigma)
    (hv : v ∈ TreeSequenceVertexSet (series.data.tree q.succ.castSucc))
    (hcomponent : ∀ w,
      w ∈ TreeSequenceVertexSet (series.data.tree q.succ.castSucc) →
      (Sum.inl w ∈ TwoColorComponent G sigma gamma delta (Sum.inl v) ↔
        w = v)) :
    ∃ selected secondStable : PartialEdgeColoring E k,
      IsProperEdgeColoring G selected ∧
      IsOneEdgeUncolored selected e0 ∧
      StableColoring (series.data.tree q.succ.castSucc)
        (TashkinovStoredColors series.data q.castSucc)
        (series.data.coloring q.castSucc) selected ∧
      IsProperEdgeColoring G secondStable ∧
      IsOneEdgeUncolored secondStable e0 ∧
      StableColoring (series.data.tree q.succ.castSucc)
        (insert delta (TashkinovStoredColors series.data q.castSucc))
        selected secondStable ∧
      series.data.coloring q.succ =
        TwoColorComponentSwap G secondStable gamma delta (Sum.inl v) ∧
      let undone := TwoColorComponentSwap G sigma gamma delta (Sum.inl v)
      StableColoring (series.data.tree q.succ.castSucc)
          (insert delta (TashkinovStoredColors series.data q.castSucc))
          secondStable undone ∧
        StableColoring (series.data.tree q.succ.castSucc)
          (insert delta (TashkinovStoredColors series.data q.castSucc))
          selected undone ∧
        StableColoring (series.data.tree q.succ.castSucc)
          (TashkinovStoredColors series.data q.castSucc)
          (series.data.coloring q.castSucc) undone := by
-- BODY
  sorry
