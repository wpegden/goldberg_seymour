import Tablet.TreeSequence

-- [TABLET NODE: TreeVertexOrder]
def TreeVertexOrder {V E : Type*} {G : LooplessMultigraph V E} {e0 : E}
    (T : TreeSequence G e0) (u v : V) : Prop :=
-- BODY
  ∃ i j : Fin (T.length + 1), T.vertex i = u ∧ T.vertex j = v ∧ i.val < j.val
