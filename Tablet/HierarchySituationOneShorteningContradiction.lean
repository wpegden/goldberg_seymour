import Tablet.GoodHierarchyTerminalPrefixRepackage
import Tablet.GoodHierarchy
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleLess
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyCounterexamplePathNumberBounds
import Tablet.HierarchyCounterexampleTailAtLeastTwo
import Tablet.HierarchyEligibleCommonMissingIndices
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyPathNumber
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchySegmentColors
import Tablet.SameGoodHierarchy
import Tablet.TashkinovAugmentation
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment

-- [TABLET NODE: HierarchySituationOneShorteningContradiction]
theorem HierarchySituationOneShorteningContradiction {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (hsituation : HierarchyPathNumber C.hierarchy = 1)
    (hlast : HierarchyFullTailLength C - 1 ∈
      HierarchyEligibleCommonMissingIndices
        G k e0 input T phi ett base C ctx) : False := by
-- BODY
  sorry
