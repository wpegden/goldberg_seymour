import Tablet.StableChangeCasesOneTwoFullTail
import Tablet.ChangeLemma
import Tablet.GoodHierarchyReservedDisjoint
import Tablet.NineN
import Tablet.HierarchyReplacementPresentationTrans
import Tablet.P2905_T2_ElementaryTerminalComponent
import Tablet.TwoColorComponentSwapMissingBehavior

-- [TABLET NODE: P2905_T2_AbsentOwnerReplacement]
theorem P2905_T2_AbsentOwnerReplacement {V E : Type*}
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
    (habsent : eta ∉ TreeMissingColors phi
      (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1))) :
    ∃ P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx,
      ∃ beta : Fin k,
        beta ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)) ∧
        beta ∈ TreeMissingColors P.coloring
          (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 2)) ∧
        (let H := P.counterexample.hierarchy
        let q := Fin.last H.dividerCount
        let Tn := P.corresponding.replacementETT.series.data.tree
          (Fin.last P.corresponding.replacementETT.rounds).castSucc
        beta ∉ (HierarchyStoredColorsAt H q).biUnion
          (P.counterexample.good.gamma q) ∪
          ((TreeSequenceVertexSet P.replacementBase.core \
              TreeSequenceVertexSet Tn).biUnion
            fun v => MissingColors G P.coloring v)) := by
-- BODY
  sorry

