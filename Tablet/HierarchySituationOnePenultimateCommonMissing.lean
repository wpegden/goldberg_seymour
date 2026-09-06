import Tablet.HierarchyClaimNine
import Tablet.HierarchyEligibleCommonMissingIndices
import Tablet.HierarchyPathNumber
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchySituationOneAdvanceInsideStored
import Tablet.HierarchySituationOneAdvanceOutsideStored

-- [TABLET NODE: HierarchySituationOnePenultimateCommonMissing]
theorem HierarchySituationOnePenultimateCommonMissing {V E : Type*}
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
    (hnonempty : (HierarchyEligibleCommonMissingIndices
      G k e0 input T phi ett base C ctx).Nonempty) :
    HierarchyFullTailLength C - 1 ∈
      HierarchyEligibleCommonMissingIndices
        G k e0 input T phi ett base C ctx := by
-- BODY
  sorry
