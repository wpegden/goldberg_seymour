import Tablet.TreeSequence
import Tablet.PartialEdgeColoring

-- [TABLET NODE: TreeColorUnusedThrough]
def TreeColorUnusedThrough {V E : Type*} {G : LooplessMultigraph V E}
    {k : ℕ} {e0 : E} (phi : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (alpha : Fin k) (j : Fin (T.length + 1)) : Prop :=
-- BODY
  ∀ r : Fin T.length, 1 ≤ r.val → r.val < j.val →
    phi (T.edge r) ≠ some alpha
