import Tablet.MissingColors
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TreeMissingColors
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponentSwap

-- [TABLET NODE: TashkinovAugmentationSequenceComponentSwap]
theorem TashkinovAugmentationSequenceComponentSwap {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (alpha beta : Fin k)
    (hne : alpha ≠ beta) (z : Sum V E)
    (X Y : TreeSequence G e0)
    (hsequence : TashkinovAugmentationSequence phi X Y)
    (halpha : alpha ∈ TreeMissingColors
      (TwoColorComponentSwap G phi alpha beta z) X)
    (hbeta : beta ∈ TreeMissingColors
      (TwoColorComponentSwap G phi alpha beta z) X) :
    TashkinovAugmentationSequence
      (TwoColorComponentSwap G phi alpha beta z) X Y := by
-- BODY
  sorry
