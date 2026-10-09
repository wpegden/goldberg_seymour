import Tablet.P2752_T2_PrefixData
import Tablet.P2752_T2_TerminalStoredColors
import Tablet.HierarchySituationTwoCaseThreeData
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyFirstMissingPosition
import Tablet.MaximumDefectiveChoice
import Tablet.MissingColors
import Tablet.OrderedTreeUnion
import Tablet.SameHierarchyStages
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeSequencePrefix
import Tablet.TreeMissingColors
import Tablet.TreeColoringInvariant
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchySegmentColors
import Tablet.HierarchyStarredStage
import Tablet.TreeSequenceVertexSet
import Tablet.TashkinovStoredColors
import Tablet.TwoColorComponentSwap

-- [TABLET NODE: P2752_T2_TerminalHierarchyRestore]
theorem P2752_T2_TerminalHierarchyRestore {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseThreeData G k e0 input T phi ett base C ctx)
    (beta : Fin k)
    (hmissing : beta ∈ TreeMissingColors phi
      (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 2)))
    (hpresent : beta ∉ MissingColors G phi (T.vertex D.terminalVertexIndex))
    (hsigma : sigma = TwoColorComponentSwap G phi D.alpha beta
      (Sum.inl (T.vertex D.terminalVertexIndex)))
    (F : P2752_T2_PrefixData C
      (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)) sigma)
    (hfixed : ∀ t : Fin T.length, sigma (T.edge t) = phi (T.edge t))
    (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T) :
    ∃ newBase : HierarchyBase corr.replacementETT sigma,
      ∃ K : TashkinovHierarchy corr.replacementETT newBase,
        ∃ good : GoodHierarchy K, SameGoodHierarchy C.good good := by
-- BODY
  sorry
