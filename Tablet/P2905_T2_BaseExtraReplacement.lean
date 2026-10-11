import Tablet.StableChangeCasesOneTwoStarredTail
import Tablet.ChangeLemma
import Tablet.GoodHierarchyReservedDisjoint
import Tablet.HierarchyStoredColorsCardinality
import Tablet.HierarchyReplacementPresentationTrans
import Tablet.P2905_T2_ElementaryTerminalComponent
import Tablet.TwoColorComponentSwapMissingBehavior

-- [TABLET NODE: P2905_T2_BaseExtraReplacement]
theorem P2905_T2_BaseExtraReplacement {V E : Type*}
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
    (hextra : alpha ∈ ((TreeSequenceVertexSet base.core \
        TreeSequenceVertexSet
          (ett.series.data.tree (Fin.last ett.rounds).castSucc)).biUnion
        fun v => MissingColors G phi v))
    (hgamma : alpha ∉ (HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount)).biUnion (C.good.gamma (Fin.last C.hierarchy.dividerCount))) :
    ∃ P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx,
      ∃ beta : Fin k,
        beta ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)) ∧
        beta ∈ TreeMissingColors P.coloring (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)) ∧
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

