import Tablet.TreeSequence
import Tablet.PartialEdgeColoring

-- [TABLET NODE: TreeUsedColors]
noncomputable def TreeUsedColors {V E : Type*} {G : LooplessMultigraph V E}
    {k : ℕ} {e0 : E} (phi : PartialEdgeColoring E k)
    (T : TreeSequence G e0) : Finset (Fin k) := by
-- BODY
  classical
  exact Finset.univ.filter fun alpha =>
    ∃ j : Fin T.length, 1 ≤ j.val ∧ phi (T.edge j) = some alpha
