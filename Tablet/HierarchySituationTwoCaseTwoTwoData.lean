import Tablet.HierarchySituationTwoCommonTailData
import Tablet.HierarchyStoredColorsAt
import Tablet.MissingColors

-- [TABLET NODE: HierarchySituationTwoCaseTwoTwoData]
structure HierarchySituationTwoCaseTwoTwoData {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C) extends
    HierarchySituationTwoCommonTailData
      G k e0 input T phi ett base C ctx where
-- BODY
  alpha : Fin k
  alphaMissingPenultimate :
    alpha ∈ MissingColors G phi (T.vertex penultimateVertexIndex)
  alphaMissingTerminal :
    alpha ∈ MissingColors G phi (T.vertex terminalVertexIndex)
  alphaOutsideStored :
    alpha ∉ HierarchyStoredColorsAt C.hierarchy
      (Fin.last C.hierarchy.dividerCount)
  thetaMissingPenultimate :
    theta ∈ MissingColors G phi (T.vertex penultimateVertexIndex)
