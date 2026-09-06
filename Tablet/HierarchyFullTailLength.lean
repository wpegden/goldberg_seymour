import Tablet.HierarchyCounterexample
import Tablet.HierarchyStarredStage

-- [TABLET NODE: HierarchyFullTailLength]
def HierarchyFullTailLength {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T phi}
    {base : HierarchyBase ett phi}
    (C : HierarchyCounterexample base) : ℕ :=
-- BODY
  let H := C.hierarchy
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  T.length - A.length
