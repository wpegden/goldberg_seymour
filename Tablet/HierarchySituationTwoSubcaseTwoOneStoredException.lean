import Tablet.ChangeLemma
import Tablet.ColoredVertexSetElementary
import Tablet.CombinedStableClosurePreserved
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchySituationTwoCaseOneData
import Tablet.HierarchySituationTwoCaseTwoData
import Tablet.HierarchySituationTwoCaseTwoExclusions
import Tablet.HierarchySituationTwoSubcaseOneOne
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyTailMissingColorExclusion
import Tablet.HierarchyWeaklyStable
import Tablet.IsOneEdgeUncolored
import Tablet.MissingColors
import Tablet.SameGoodHierarchy
import Tablet.StableColoring
import Tablet.StableChangeCasesOneTwo
import Tablet.StableChangeCasesOneTwoFullTail
import Tablet.TashkinovHierarchy
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorPathComponent
import Tablet.sc2

-- [TABLET NODE: HierarchySituationTwoSubcaseTwoOneStoredException]
theorem HierarchySituationTwoSubcaseTwoOneStoredException {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseTwoData
      G k e0 input T phi ett base C ctx)
    (eta : Fin k)
    (hetaStored : eta ∈ HierarchyStoredColorsAt C.hierarchy
      (Fin.last C.hierarchy.dividerCount))
    (hetaMissing :
      eta ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex))
    (hthetaPair :
      D.theta ∈ C.good.gamma (Fin.last C.hierarchy.dividerCount) eta) :
    False := by
-- BODY
  sorry
