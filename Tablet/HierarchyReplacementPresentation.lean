import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.HierarchyCounterexample
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.MaximumProperty
import Tablet.SameGoodHierarchy

-- [TABLET NODE: HierarchyReplacementPresentation]
structure HierarchyReplacementPresentation {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C) where
-- BODY
  coloring : PartialEdgeColoring E k
  corresponding : CorrespondingExtendedTashkinovTree
    G k e0 ett coloring T
  maximum : MaximumProperty corresponding.replacementETT
  replacementBase : HierarchyBase corresponding.replacementETT coloring
  counterexample : HierarchyCounterexample replacementBase
  sameGood : SameGoodHierarchy C.good counterexample.good
  minimumContext : HierarchyMinimumCounterexampleContext
    G k e0 corresponding.replacementInput T coloring
      corresponding.replacementETT replacementBase counterexample
