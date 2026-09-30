import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.MaximumDefectiveChoice
import Tablet.MissingColors
import Tablet.ParallelExtensionColor
import Tablet.PresentColors
import Tablet.sc2
import Tablet.StableColoring
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeExit
import Tablet.TreeExitPath
import Tablet.TreeSequenceInitialSegment
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorPathComponent

-- [TABLET NODE: ParallelStepRootComponentSetup]
theorem ParallelStepRootComponentSetup {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k}
    (series : TashkinovSeries G k rounds e0 input)
    (t : Fin rounds) (support : V) (gamma delta : Fin k)
    (htKind : series.data.kind t.succ =
      some TashkinovExtensionKind.PE)
    (htVertex : series.data.chosenVertex t.succ = some support)
    (htGamma : series.data.gamma t.succ = some gamma)
    (htDelta : series.data.delta t.succ = some delta) :
    gamma ≠ delta ∧
      IsProperEdgeColoring G (series.data.coloring t.succ) ∧
      TreeSequenceInitialSegment
        (series.data.tree t.succ.castSucc)
        (series.data.tree t.succ.succ) ∧
      support ∈
        TreeSequenceVertexSet (series.data.tree t.succ.castSucc) ∧
      TwoColorPathComponent G (series.data.coloring t.succ)
        gamma delta (Sum.inl support) ∧
      (∀ w : V,
        w ∈ TreeSequenceVertexSet (series.data.tree t.succ.castSucc) →
        (Sum.inl w ∈ TwoColorComponent G
            (series.data.coloring t.succ) gamma delta
            (Sum.inl support) ↔ w = support)) ∧
      ∀ v : V,
        v ∈ TreeSequenceVertexSet (series.data.tree t.succ.castSucc) →
        v ≠ support →
        ∃ f : E, Sum.inr f ∈ TwoColorComponent G
          (series.data.coloring t.succ) gamma delta (Sum.inl v) := by
-- BODY
  sorry
