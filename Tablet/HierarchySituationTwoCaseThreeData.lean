import Tablet.HierarchySituationTwoCommonTailData
import Tablet.MissingColors

-- [TABLET NODE: HierarchySituationTwoCaseThreeData]
structure HierarchySituationTwoCaseThreeData {V E : Type*}
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
  alphaMissingTerminal :
    alpha ∈ MissingColors G phi (T.vertex terminalVertexIndex)
  earlierVertexIndex : Fin (T.length + 1)
  earlierVertexBeforePenultimate :
    earlierVertexIndex.val < penultimateVertexIndex.val
  alphaMissingEarlier :
    alpha ∈ MissingColors G phi (T.vertex earlierVertexIndex)
