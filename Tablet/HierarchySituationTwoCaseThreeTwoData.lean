import Tablet.HierarchySituationTwoCaseThreeNormalizedData
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.MissingColors

-- [TABLET NODE: HierarchySituationTwoCaseThreeTwoData]
structure HierarchySituationTwoCaseThreeTwoData {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C) extends
    HierarchySituationTwoCaseThreeNormalizedData
      G k e0 input T phi ett base C ctx where
-- BODY
  thetaMissingPenultimate :
    theta ∈ MissingColors G phi (T.vertex penultimateVertexIndex)
