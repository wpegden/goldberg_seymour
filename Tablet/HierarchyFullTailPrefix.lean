import Tablet.HierarchyCounterexample
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyStarredStage
import Tablet.TreeSequencePrefix

-- [TABLET NODE: HierarchyFullTailPrefix]
noncomputable def HierarchyFullTailPrefix {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T phi}
    {base : HierarchyBase ett phi}
    (C : HierarchyCounterexample base) (i : ℕ) : TreeSequence G e0 :=
-- BODY
  let H := C.hierarchy
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  TreeSequencePrefix T (min (A.length + i) T.length)
    (by
      have hA := A.positive
      have hT := T.positive
      omega)
    (Nat.min_le_right _ _)
