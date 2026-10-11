import Tablet.StableChangeCasesOneTwoSplitTail
import Tablet.ChangeLemma
import Tablet.GoodHierarchyReservedDisjoint
import Tablet.HierarchyTailMissingColorExclusion
import Tablet.HierarchyNonparallelFirstEdge
import Tablet.HierarchyReplacementPresentationTrans
import Tablet.P2905_T2_ElementaryTerminalComponent
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.P2813_T1_TerminalRoute
import Tablet.P2813_T1_BaseDisplayedEdges
import Tablet.TashkinovAugmentationSequenceSuffix
import Tablet.TashkinovAugmentationSequenceColoringTransport

-- [TABLET NODE: P2905_T2_LateOwnerReplacement]
theorem P2905_T2_LateOwnerReplacement {V E : Type*}
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
    (hpathUpper : HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C)
    (alpha : Fin k)
    (hterminal : alpha ∈ MissingColors G phi (T.vertex (Fin.last T.length)))
    (hstar : alpha ∈ TreeMissingColors phi (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)))
    (eta : Fin k) (heta : eta ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount))
    (hgamma : alpha ∈ C.good.gamma (Fin.last C.hierarchy.dividerCount) eta)
    (t : ℕ) (htpos : 1 ≤ t) (htupper : t < HierarchyFullTailLength C)
    (htlate : HierarchyPathNumber C.hierarchy - 1 ≤ t)
    (hfirst : (HierarchyFirstMissingPosition phi T eta).val =
      (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length + t)
    (hmissing : eta ∈ MissingColors G phi
      ((HierarchyFullTailPrefix C t).vertex
        (Fin.last (HierarchyFullTailPrefix C t).length))) :
    ∃ P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx,
      eta ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)) ∧
      eta ∈ MissingColors G P.coloring
        ((HierarchyFullTailPrefix C t).vertex
          (Fin.last (HierarchyFullTailPrefix C t).length)) := by
-- BODY
  sorry

