import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.HierarchyBase
import Tablet.HierarchyClaimNineFirstUseAfterSeed
import Tablet.HierarchyClaimNineFirstUseSeed
import Tablet.HierarchyClaimNinePENormalization
import Tablet.HierarchyClaimNineUnusedTailColor
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleTailAtLeastTwo
import Tablet.HierarchyCounterexampleTerminalCommonMissing
import Tablet.HierarchyEligibleCommonMissingIndices
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyPathNumber
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchyStarredStage
import Tablet.SameGoodHierarchy
import Tablet.SameHierarchyStages

-- [TABLET NODE: HierarchyClaimNine]
theorem HierarchyClaimNine {V E : Type*}
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
        ∀ v : V, (MissingColors G mu v).Nonempty) :
    (HierarchyEligibleCommonMissingIndices
      G k e0 input T phi ett base C ctx).Nonempty := by
-- BODY
  sorry
