import Tablet.ChangeLemma
import Tablet.ColoredVertexSetElementary
import Tablet.CombinedStableClosurePreserved
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleLess
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchySituationTwoCaseOneData
import Tablet.HierarchySituationTwoReorderedTreesCertified
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyStoredColorsCardinality
import Tablet.HierarchySituationTwoTailData
import Tablet.HierarchyWeaklyStable
import Tablet.MaximumPropertyTransport
import Tablet.MissingColors
import Tablet.ModColoring
import Tablet.NineN
import Tablet.OrderedTreeUnion
import Tablet.SameGoodHierarchy
import Tablet.StableChangeCasesOneTwo
import Tablet.StableChangeCasesOneTwoFullTail
import Tablet.StableChangeCasesOneTwoSplitTail
import Tablet.TashkinovAugmentationSequenceColoringTransport
import Tablet.TashkinovHierarchy
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorPathComponent
import Tablet.sc2

-- [TABLET NODE: HierarchySituationTwoSubcaseOneOneStoredException]
theorem HierarchySituationTwoSubcaseOneOneStoredException {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseOneData
      G k e0 input T phi ett base C ctx)
    (eta : Fin k)
    (hetaStored : eta ∈ HierarchyStoredColorsAt C.hierarchy
      (Fin.last C.hierarchy.dividerCount))
    (hthetaPair :
      D.theta ∈ C.good.gamma (Fin.last C.hierarchy.dividerCount) eta)
    (hetaMissing :
      eta ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex)) :
    False := by
-- BODY
  sorry
