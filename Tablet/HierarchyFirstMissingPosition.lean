import Tablet.MissingColors
import Tablet.TreeSequence

-- [TABLET NODE: HierarchyFirstMissingPosition]
noncomputable def HierarchyFirstMissingPosition {V E : Type*}
    [Fintype V] [Fintype E] {G : LooplessMultigraph V E} {k : ℕ}
    {e0 : E} (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (eta : Fin k) : Fin (T.length + 1) := by
-- BODY
  classical
  let candidates : Finset (Fin (T.length + 1)) :=
    Finset.univ.filter fun i => eta ∈ MissingColors G phi (T.vertex i)
  exact if h : candidates.Nonempty then candidates.min' h else Fin.last T.length
