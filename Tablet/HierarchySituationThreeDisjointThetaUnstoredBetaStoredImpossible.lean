import Tablet.ChangeLemma
import Tablet.ColoredVertexSetElementary
import Tablet.CombinedStableClosurePreserved
import Tablet.CombinedStableColoring
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyEligibleCommonMissingIndices
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyPathNumber
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchyReplacementPresentationTrans
import Tablet.HierarchySegmentColors
import Tablet.HierarchySituationThreeDisjointData
import Tablet.HierarchySituationThreeEligibleIndexBound
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyTailMissingColorExclusion
import Tablet.HierarchyWeaklyStable
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MissingColorIncidenceEndpoint
import Tablet.MissingColors
import Tablet.ModColoring
import Tablet.OrderedTreeUnion
import Tablet.PresentColors
import Tablet.SameGoodHierarchy
import Tablet.StableChangeCasesOneTwo
import Tablet.StableChangeCasesOneTwoSplitTail
import Tablet.StableColoring
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceColoringTransport
import Tablet.TashkinovAugmentationSequenceComponentSwap
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovClosure
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeColoringInvariant
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorPathComponent

-- [TABLET NODE: HierarchySituationThreeDisjointThetaUnstoredBetaStoredImpossible]
theorem HierarchySituationThreeDisjointThetaUnstoredBetaStoredImpossible
    {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx)
    (alpha beta : Fin k)
    (hpathLower : 2 <= HierarchyPathNumber C.hierarchy)
    (hpathUpper :
      HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C)
    (hvertexMissing : forall (mu : PartialEdgeColoring E k),
      IsProperEdgeColoring G mu -> IsOneEdgeUncolored mu e0 ->
        forall v : V, (MissingColors G mu v).Nonempty)
    (d : HierarchySituationThreeDisjointData
      G k e0 input T phi ett base C ctx P alpha beta)
    (hthetaUnstored :
      let H := d.switched.counterexample.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      d.theta ∉ HierarchyStoredColorsAt H q)
    (hconditionStored :
      let H := d.switched.counterexample.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let A := HierarchyStarredStage H q
      let j := HierarchyPathNumber C.hierarchy
      let B := HierarchyFullTailPrefix C (j - 2)
      let D := HierarchyStoredColorsAt H q
      let tailUsedThroughJ :=
        (Finset.univ : Finset (Fin k)).filter fun c =>
          exists r : Fin T.length,
            A.length <= r.val ∧ r.val < A.length + j ∧
              d.switched.coloring (T.edge r) = some c
      beta ∈ D ∧ beta ∈ TreeMissingColors d.switched.coloring B ∧
        Disjoint (d.switched.counterexample.good.gamma q beta ∪ {beta})
          tailUsedThroughJ) : False := by
-- BODY
  sorry
