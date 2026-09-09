import Tablet.CorrespondingExtendedTashkinovTreeTrans
import Tablet.HierarchyReplacementPresentation

-- [TABLET NODE: HierarchyReplacementPresentationTrans]
lemma HierarchyReplacementPresentationTrans
    {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx)
    (tau : PartialEdgeColoring E k)
    (second : CorrespondingExtendedTashkinovTree G k e0
      P.corresponding.replacementETT tau T)
    (baseSecond : HierarchyBase second.replacementETT tau)
    (CSecond : HierarchyCounterexample baseSecond)
    (sameGoodSecond : SameGoodHierarchy
      P.counterexample.good CSecond.good) :
    Exists fun PSecond : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx =>
        PSecond.coloring = tau := by
-- BODY
  sorry
