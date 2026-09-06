import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyFullTailLength
import Tablet.HierarchySituationTwoTailData
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceEdgeSet
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: HierarchySituationTwoReorderedTrees]
structure HierarchySituationTwoReorderedTrees {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (D : HierarchySituationTwoTailData
      G k e0 input T phi ett base C ctx) where
-- BODY
  penultimateEdgeIndex : Fin T.length
  penultimateEdgePosition : penultimateEdgeIndex.val + 2 = T.length
  minus : TreeSequence G e0
  star : TreeSequence G e0
  originalPenultimate : TreeSequenceAdjoinEdge
    (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 2))
    (T.edge penultimateEdgeIndex)
    (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1))
  originalFinal : TreeSequenceAdjoinEdge
    (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1))
    (T.edge D.lastEdgeIndex) T
  minusFinal : TreeSequenceAdjoinEdge
    (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 2))
    (T.edge D.lastEdgeIndex) minus
  minusTerminalVertex :
    minus.vertex (Fin.last minus.length) = T.vertex D.terminalVertexIndex
  starFinal : TreeSequenceAdjoinEdge minus
    (T.edge penultimateEdgeIndex) star
  starPenultimateVertex :
    star.vertex (Fin.last star.length) = T.vertex D.penultimateVertexIndex
  minusVertexSet : TreeSequenceVertexSet minus =
    TreeSequenceVertexSet T \ {T.vertex D.penultimateVertexIndex}
  minusEdgeSet : TreeSequenceEdgeSet minus =
    TreeSequenceEdgeSet T \ {T.edge penultimateEdgeIndex}
  starVertexSet : TreeSequenceVertexSet star = TreeSequenceVertexSet T
  starEdgeSet : TreeSequenceEdgeSet star = TreeSequenceEdgeSet T
