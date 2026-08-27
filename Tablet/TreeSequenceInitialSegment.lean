import Tablet.TreeSequence

-- [TABLET NODE: TreeSequenceInitialSegment]
def TreeSequenceInitialSegment {V E : Type*} {G : LooplessMultigraph V E}
    {e0 : E} (T T' : TreeSequence G e0) : Prop :=
-- BODY
  ∃ hlen : T.length ≤ T'.length,
    (∀ i : Fin (T.length + 1),
      T'.vertex (Fin.castLE (Nat.succ_le_succ hlen) i) = T.vertex i) ∧
    ∀ j : Fin T.length, T'.edge (Fin.castLE hlen j) = T.edge j
