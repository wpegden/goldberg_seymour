import Tablet.HierarchyEligibleCommonMissingIndices
import Tablet.ChangeLemma
import Tablet.HierarchyClaimNinePENormalization
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyCounterexampleTailAtLeastTwo
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyTailMissingColorExclusion
import Tablet.SameGoodHierarchy
import Tablet.StableChangeCasesOneTwoFullTail
import Tablet.TwoColorPathComponent
import Tablet.TreeMissingColors

-- [TABLET NODE: HierarchyClaimNineUnusedTailColor]
theorem HierarchyClaimNineUnusedTailColor {V E : Type*}
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
    (hstart :
      let H := P.counterexample.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      alpha ∈ TreeMissingColors P.coloring A ∧
        alpha ∈ MissingColors G P.coloring
          (T.vertex (Fin.last T.length)))
    (hnormalized :
      let H := P.counterexample.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
        Fin.last P.corresponding.replacementETT.rounds
      let Tnq := H.stage ⟨H.dividerCount, by omega⟩
      let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
      (0 < H.dividerCount ∧ alpha ∈ TreeMissingColors P.coloring Tnq) ∨
        (H.dividerCount = 0 ∧ alpha ∈ TreeMissingColors P.coloring Tn))
    (hnoCommon : ∀ i ∈ Finset.Icc 1 (HierarchyFullTailLength C - 1),
      Disjoint
        (MissingColors G P.coloring
          ((HierarchyFullTailPrefix C i).vertex
            (Fin.last (HierarchyFullTailPrefix C i).length)))
        (MissingColors G P.coloring (T.vertex (Fin.last T.length))))
    (hunused :
      let A := HierarchyStarredStage P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount)
      ∀ t : Fin T.length, A.length ≤ t.val →
        P.coloring (T.edge t) ≠ some alpha) :
    (HierarchyEligibleCommonMissingIndices
      G k e0 input T phi ett base C ctx).Nonempty := by
-- BODY
  sorry
