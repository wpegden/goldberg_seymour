import Tablet.HierarchyEligibleCommonMissingIndices
import Tablet.ChangeLemma
import Tablet.GoodHierarchy
import Tablet.HierarchyClaimNinePENormalization
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyPathNumber
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyTailMissingColorExclusion
import Tablet.SameGoodHierarchy
import Tablet.StableChangeCasesOneTwoFullTail

-- [TABLET NODE: HierarchySituationOneAdvanceInsideStored]
theorem HierarchySituationOneAdvanceInsideStored {V E : Type*}
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
    (hvertexMissing : ∀ (mu : PartialEdgeColoring E k),
      IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
        ∀ v : V, (MissingColors G mu v).Nonempty)
    (i : ℕ) (hiLower : 1 ≤ i)
    (hiUpper : i < HierarchyFullTailLength C - 1)
    (P : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx)
    (alpha : Fin k)
    (hcommon :
      alpha ∈ MissingColors G P.coloring
          ((HierarchyFullTailPrefix C i).vertex
            (Fin.last (HierarchyFullTailPrefix C i).length)) ∧
        alpha ∈ MissingColors G P.coloring
          (T.vertex (Fin.last T.length)))
    (hinside :
      let H := P.counterexample.hierarchy
      alpha ∈ HierarchyStoredColorsAt H (Fin.last H.dividerCount)) :
    i + 1 ∈ HierarchyEligibleCommonMissingIndices
      G k e0 input T phi ett base C ctx := by
-- BODY
  sorry
