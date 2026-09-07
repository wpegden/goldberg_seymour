import Tablet.ChangeLemma
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyCounterexampleTerminalCommonMissing
import Tablet.HierarchyEligibleCommonMissingIndices
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyNonparallelFirstEdge
import Tablet.HierarchyPathNumber
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchySituationThreeClaimJMinusOneNonempty
import Tablet.HierarchySituationThreeEligibleIndexBound
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MissingColorIncidenceEndpoint
import Tablet.MissingColors
import Tablet.NineN
import Tablet.SameGoodHierarchy
import Tablet.StableChangeCasesOneTwo
import Tablet.StableChangeCasesOneTwoSplitTail
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovSeriesStep
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: HierarchySituationThreeClaimJMinusOneEmpty]
theorem HierarchySituationThreeClaimJMinusOneEmpty {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (hpathLower : 2 ≤ HierarchyPathNumber C.hierarchy)
    (hpathUpper :
      HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C)
    (hvertexMissing : ∀ (mu : PartialEdgeColoring E k),
      IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
        ∀ v : V, (MissingColors G mu v).Nonempty)
    (hempty : ¬ (HierarchyEligibleCommonMissingIndices
      G k e0 input T phi ett base C ctx).Nonempty) :
    ∃ P : HierarchyReplacementPresentation
        G k e0 input T phi ett base C ctx,
      ∃ alpha : Fin k,
        let H := P.counterexample.hierarchy
        let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
        let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
          Fin.last P.corresponding.replacementETT.rounds
        let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
        let B := HierarchyFullTailPrefix C
          (HierarchyPathNumber C.hierarchy - 2)
        let D := HierarchyStoredColorsAt H q
        let Gamma := D.biUnion (P.counterexample.good.gamma q)
        let baseExtraMissing :=
          ((TreeSequenceVertexSet P.replacementBase.core \
              TreeSequenceVertexSet Tn).biUnion
            fun v => MissingColors G P.coloring v)
        alpha ∈ MissingColors G P.coloring
            (T.vertex (Fin.last T.length)) ∧
          alpha ∈ TreeMissingColors P.coloring B ∧
          (alpha ∉ Gamma ∪ baseExtraMissing ∨
            ∃ eta : Fin k, eta ∈ D ∧
              alpha ∈ P.counterexample.good.gamma q eta ∧
              (HierarchyFirstMissingPosition P.coloring T eta).val ≤
                B.length) := by
-- BODY
  sorry
