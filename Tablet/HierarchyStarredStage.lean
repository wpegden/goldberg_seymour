import Tablet.TashkinovHierarchy

-- [TABLET NODE: HierarchyStarredStage]
def HierarchyStarredStage {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T generating}
    {base : HierarchyBase ett phi} (H : TashkinovHierarchy ett base)
    (j : Fin (H.dividerCount + 1)) : TreeSequence G e0 :=
-- BODY
  Fin.cases base.core
    (fun i : Fin H.dividerCount => H.stage i.succ.castSucc) j
