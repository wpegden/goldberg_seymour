import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.HierarchyBase
import Tablet.HierarchyBaseCorrespondingTransport
import Tablet.MaximumDefectiveChoice
import Tablet.sc2
import Tablet.StableColoring
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors

-- [TABLET NODE: GoodHierarchyCommonOriginalBaseTransport]
theorem GoodHierarchyCommonOriginalBaseTransport {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (J U : TreeSequence G e0)
    (corrJ : CorrespondingExtendedTashkinovTree G k e0 ett sigma J)
    (baseJ : HierarchyBase corrJ.replacementETT sigma)
    (corrU : CorrespondingExtendedTashkinovTree G k e0 ett sigma U) :
    ∃ baseU : HierarchyBase corrU.replacementETT sigma,
      baseU.core = baseJ.core ∧
      baseU.closure = baseJ.closure ∧
      baseU.supportPosition.val = baseJ.supportPosition.val := by
-- BODY
  sorry
