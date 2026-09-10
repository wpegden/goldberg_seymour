import Tablet.OrderedTreeUnion

-- [TABLET NODE: OrderedTreeUnionExists]
theorem OrderedTreeUnionExists
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : LooplessMultigraph V E} {e0 : E}
    (A B : TreeSequence G e0) :
    exists U : TreeSequence G e0, Nonempty (OrderedTreeUnion A B U) := by
-- BODY
  sorry
