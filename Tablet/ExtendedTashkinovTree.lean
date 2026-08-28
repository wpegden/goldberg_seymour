import Tablet.TashkinovSeries
import Tablet.TreeSequenceInitialSegment

-- [TABLET NODE: ExtendedTashkinovTree]
structure ExtendedTashkinovTree {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k) where
-- BODY
  rounds : ℕ
  roundsPositive : 1 ≤ rounds
  series : TashkinovSeries G k rounds e0 input
  abovePenultimate : TreeSequenceInitialSegment
    (series.data.tree ⟨rounds, by omega⟩) T
  strictAbovePenultimate :
    (series.data.tree ⟨rounds, by omega⟩).length < T.length
  belowFinal : TreeSequenceInitialSegment T
    (series.data.tree (Fin.last (rounds + 1)))
  generatingColoring : generating = series.data.coloring (Fin.last rounds)
