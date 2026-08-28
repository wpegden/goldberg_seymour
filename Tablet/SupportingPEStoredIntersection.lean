import Tablet.HkuUnsupportedVertexColors
import Tablet.MaximumDefectiveChoice
import Tablet.MissingColors
import Tablet.ParallelExtensionColor
import Tablet.StableColoring
import Tablet.SupportingPEColorChain
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponentSwap

-- [TABLET NODE: SupportingPEStoredIntersection]
theorem SupportingPEStoredIntersection {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k rounds p : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input) (q : Fin rounds) (u : V)
    (hu : u ∈ TreeSequenceVertexSet (series.data.tree q.succ.castSucc))
    (indices : Fin (p + 1) → Fin rounds)
    (hincreasing : ∀ a b, a.val < b.val →
      (indices a).val < (indices b).val)
    (henumerates : ∀ j : Fin rounds,
      (j.val ≤ q.val ∧
        series.data.kind j.succ = some TashkinovExtensionKind.PE ∧
        series.data.chosenVertex j.succ = some u) ↔
      ∃ a : Fin (p + 1), indices a = j)
    (deltaLast : Fin k)
    (hdeltaLast : series.data.delta (indices (Fin.last p)).succ = some deltaLast) :
    let storedPairs := Finset.univ.biUnion fun a : Fin (p + 1) =>
      series.data.stored (indices a).succ
    MissingColors G (series.data.coloring q.succ) u ∩ storedPairs = {deltaLast} ∧
      MissingColors G
          (series.data.coloring (indices (Fin.last p)).succ) u ∩ storedPairs =
        {deltaLast} := by
-- BODY
  sorry
