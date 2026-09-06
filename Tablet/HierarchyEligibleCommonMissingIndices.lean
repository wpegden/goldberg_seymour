import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyReplacementPresentation
import Tablet.MissingColors

-- [TABLET NODE: HierarchyEligibleCommonMissingIndices]
noncomputable def HierarchyEligibleCommonMissingIndices {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C) : Finset ℕ := by
-- BODY
  classical
  exact (Finset.Icc 1 (HierarchyFullTailLength C - 1)).filter fun i =>
    ∃ P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx,
      ∃ alpha : Fin k,
        alpha ∈ MissingColors G P.coloring
            ((HierarchyFullTailPrefix C i).vertex
              (Fin.last (HierarchyFullTailPrefix C i).length)) ∧
          alpha ∈ MissingColors G P.coloring
            (T.vertex (Fin.last T.length))
