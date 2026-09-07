import Tablet.ChangeLemma
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.GoodHierarchyReservedDisjoint
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleLess
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyLEMStable
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchySituationTwoCaseThreeData
import Tablet.HierarchySituationTwoCaseThreeNormalizedData
import Tablet.HierarchySituationTwoCommonTailData
import Tablet.HierarchySituationTwoOutsidePenultimateReconstruction
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.MaximumPropertyTransport
import Tablet.ModColoring
import Tablet.NineN
import Tablet.StableChangeCasesOneTwoFullTail
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovClosure
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.Td
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorIncidenceDegreeAtMostTwo

-- [TABLET NODE: HierarchySituationTwoCaseThreeNormalization]
theorem HierarchySituationTwoCaseThreeNormalization {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseThreeData
      G k e0 input T phi ett base C ctx) :
    ∃ P : HierarchyReplacementPresentation
        G k e0 input T phi ett base C ctx,
      Nonempty (HierarchySituationTwoCaseThreeNormalizedData
        G k e0 P.corresponding.replacementInput T P.coloring
          P.corresponding.replacementETT P.replacementBase
          P.counterexample P.minimumContext) := by
-- BODY
  sorry
