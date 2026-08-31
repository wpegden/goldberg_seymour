import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyStarredStage

-- [TABLET NODE: HierarchySegmentColors]
noncomputable def HierarchySegmentColors {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T generating}
    {base : HierarchyBase ett phi} (H : TashkinovHierarchy ett base)
    (j : Fin (H.dividerCount + 1)) (eta : Fin k) : Finset (Fin k) := by
-- BODY
  classical
  let A := HierarchyStarredStage H j
  let B := H.stage j.succ
  let p := HierarchyFirstMissingPosition phi T eta
  exact Finset.univ.filter fun c =>
    ∃ r : Fin B.length, A.length ≤ r.val ∧
      r.val < min p.val B.length ∧ phi (B.edge r) = some c
