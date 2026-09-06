import Tablet.HierarchyFullTailLength
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyPathNumber
import Tablet.Incident
import Tablet.MissingColors

-- [TABLET NODE: HierarchySituationTwoTailData]
structure HierarchySituationTwoTailData {V E : Type*}
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
  tailAtLeastTwo : 2 ≤ HierarchyFullTailLength C
  pathNumberFull :
    HierarchyPathNumber C.hierarchy = HierarchyFullTailLength C
  lastEdgeIndex : Fin T.length
  penultimateVertexIndex : Fin (T.length + 1)
  terminalVertexIndex : Fin (T.length + 1)
  lastEdgePosition : lastEdgeIndex.val + 1 = T.length
  penultimateVertexPosition :
    penultimateVertexIndex.val + 1 = T.length
  terminalVertexPosition : terminalVertexIndex.val = T.length
  lastEdgeNotIncidentPenultimate :
    ¬ Incident G (T.vertex penultimateVertexIndex) (T.edge lastEdgeIndex)
  theta : Fin k
  thetaOnLastEdge : phi (T.edge lastEdgeIndex) = some theta
  thetaPresentPenultimate :
    theta ∉ MissingColors G phi (T.vertex penultimateVertexIndex)
