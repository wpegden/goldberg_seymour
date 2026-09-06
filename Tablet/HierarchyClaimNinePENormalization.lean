import Tablet.HierarchyEligibleCommonMissingIndices
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyCounterexampleTailAtLeastTwo
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyStoredColorsCardinality
import Tablet.HierarchyTailMissingColorExclusion
import Tablet.SameGoodHierarchy
import Tablet.StableChangeCasesOneTwoFullTail
import Tablet.TashkinovExtensionKind
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorPathComponent
import Tablet.interchange
import Tablet.TreeMissingColors

-- [TABLET NODE: HierarchyClaimNinePENormalization]
theorem HierarchyClaimNinePENormalization {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (hvertexMissing : ∀ (mu : PartialEdgeColoring E k),
      IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
        ∀ v : V, (MissingColors G mu v).Nonempty)
    (P : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx)
    (alpha : Fin k)
    (hzero : P.counterexample.hierarchy.dividerCount = 0)
    (hpe : P.corresponding.replacementETT.series.data.kind
        (Fin.last P.corresponding.replacementETT.rounds) =
          some TashkinovExtensionKind.PE)
    (hstart :
      let H := P.counterexample.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      alpha ∈ TreeMissingColors P.coloring A ∧
        alpha ∈ MissingColors G P.coloring
          (T.vertex (Fin.last T.length)))
    (hnotTerminalLadder :
      let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
        Fin.last P.corresponding.replacementETT.rounds
      let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
      alpha ∉ TreeMissingColors P.coloring Tn)
    (hnoCommon : ∀ i ∈ Finset.Icc 1 (HierarchyFullTailLength C - 1),
      Disjoint
        (MissingColors G P.coloring
          ((HierarchyFullTailPrefix C i).vertex
            (Fin.last (HierarchyFullTailPrefix C i).length)))
        (MissingColors G P.coloring (T.vertex (Fin.last T.length)))) :
    (HierarchyEligibleCommonMissingIndices
        G k e0 input T phi ett base C ctx).Nonempty ∨
      ∃ P' : HierarchyReplacementPresentation
          G k e0 input T phi ett base C ctx,
        ∃ beta : Fin k,
          let ett' := P'.corresponding.replacementETT
          let n' : Fin (ett'.rounds + 1) := Fin.last ett'.rounds
          let Tn' := ett'.series.data.tree n'.castSucc
          let H' := P'.counterexample.hierarchy
          let A' := HierarchyStarredStage H' (Fin.last H'.dividerCount)
          beta ∈ TreeMissingColors P'.coloring Tn' ∧
            beta ∈ TreeMissingColors P'.coloring A' ∧
            beta ∈ MissingColors G P'.coloring
              (T.vertex (Fin.last T.length)) ∧
            ∀ i ∈ Finset.Icc 1 (HierarchyFullTailLength C - 1),
              Disjoint
                (MissingColors G P'.coloring
                  ((HierarchyFullTailPrefix C i).vertex
                    (Fin.last (HierarchyFullTailPrefix C i).length)))
                (MissingColors G P'.coloring
                  (T.vertex (Fin.last T.length))) := by
-- BODY
  sorry
