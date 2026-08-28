import Tablet.HkuUnsupportedVertexColors
import Tablet.MissingColors
import Tablet.MaximumDefectiveChoice
import Tablet.ParallelExtensionColor
import Tablet.StableColoring
import Tablet.SupportingPEColorChain
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponentSwap

-- [TABLET NODE: SupportingPEMissingTransport]
theorem SupportingPEMissingTransport {V E : Type*}
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
    (gammaFirst deltaLast : Fin k)
    (hgammaFirst : series.data.gamma (indices 0).succ = some gammaFirst)
    (hdeltaLast : series.data.delta (indices (Fin.last p)).succ = some deltaLast) :
    MissingColors G (series.data.coloring (indices 0).castSucc) u =
        (MissingColors G
            (series.data.coloring (indices (Fin.last p)).succ) u \ {deltaLast}) ∪
          {gammaFirst} ∧
      MissingColors G
          (series.data.coloring (indices (Fin.last p)).succ) u =
        (MissingColors G (series.data.coloring (indices 0).castSucc) u \
            {gammaFirst}) ∪ {deltaLast} := by
-- BODY
  sorry
