import Tablet.HierarchyStarredStage
import Tablet.TashkinovStoredColors
import Tablet.TreeMissingColors

-- [TABLET NODE: HierarchyStoredColorsAt]
noncomputable def HierarchyStoredColorsAt {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T generating}
    {base : HierarchyBase ett phi} (H : TashkinovHierarchy ett base)
    (j : Fin (H.dividerCount + 1)) : Finset (Fin k) := by
-- BODY
  classical
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  exact TashkinovStoredColors ett.series.data n \
    TreeMissingColors phi (HierarchyStarredStage H j)
