import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ExtendedTashkinovTree
import Tablet.MaximumProperty
import Tablet.MaximumPropertyTransport
import Tablet.ModColoring
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceInitialSegment
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovClosure
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment

-- [TABLET NODE: RestrictedAugmentationCorrespondingEndpoint]
theorem RestrictedAugmentationCorrespondingEndpoint {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hmod : ModColoring ett sigma) (hMP : MaximumProperty ett)
    (J U : TreeSequence G e0)
    (corrJ : CorrespondingExtendedTashkinovTree G k e0 ett sigma J)
    (hJU : TashkinovAugmentationSequence sigma J U) :
    ∃ corrU : CorrespondingExtendedTashkinovTree G k e0 ett sigma U,
      MaximumProperty corrU.replacementETT := by
-- BODY
  sorry
