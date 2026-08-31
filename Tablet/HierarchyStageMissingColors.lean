import Tablet.HierarchyStarredStage
import Tablet.TreeMissingColors

-- [TABLET NODE: HierarchyStageMissingColors]
noncomputable def HierarchyStageMissingColors {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T generating}
    {base : HierarchyBase ett phi} (H : TashkinovHierarchy ett base)
    (j : Fin (H.dividerCount + 1)) : Finset (Fin k) := by
-- BODY
  classical
  let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
  exact Fin.cases (TreeMissingColors phi Tn)
    (fun i : Fin H.dividerCount =>
      TreeMissingColors phi (H.stage i.succ.castSucc)) j
