import Tablet.TreeSequenceEdgeSet
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: OrderedTreeUnion]
structure OrderedTreeUnion {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V]
    {G : LooplessMultigraph V E} {e0 : E}
    (left right union : TreeSequence G e0) where
-- BODY
  leftSegment : TreeSequenceInitialSegment left union
  vertexSet : TreeSequenceVertexSet union =
    TreeSequenceVertexSet left ∪ TreeSequenceVertexSet right
  newEntryFromRight : ∀ j : Fin union.length, left.length ≤ j.val →
    ∃ i : Fin right.length,
      union.edge j = right.edge i ∧ union.vertex j.succ = right.vertex i.succ
  everyNewRightEntry : ∀ i : Fin right.length,
    right.vertex i.succ ∉ TreeSequenceVertexSet left →
    ∃ j : Fin union.length, left.length ≤ j.val ∧
      union.edge j = right.edge i ∧ union.vertex j.succ = right.vertex i.succ
  rightOrder : ∀ i j : Fin right.length,
    right.vertex i.succ ∉ TreeSequenceVertexSet left →
    right.vertex j.succ ∉ TreeSequenceVertexSet left → i.val < j.val →
    ∀ p q : Fin union.length,
      union.vertex p.succ = right.vertex i.succ →
      union.vertex q.succ = right.vertex j.succ → p.val < q.val
