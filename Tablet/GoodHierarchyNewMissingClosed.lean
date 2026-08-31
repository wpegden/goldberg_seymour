import Tablet.ColoredVertexSetElementary
import Tablet.GoodHierarchy
import Tablet.HierarchyStoredColorsAntitone

-- [TABLET NODE: GoodHierarchyNewMissingClosed]
theorem GoodHierarchyNewMissingClosed {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T generating}
    {base : HierarchyBase ett phi} {H : TashkinovHierarchy ett base}
    (good : GoodHierarchy H) (i : Fin H.dividerCount)
    (helementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet (H.stage i.succ.castSucc)))
    (alpha : Fin k)
    (halpha : alpha ∈
      ((TreeSequenceVertexSet (H.stage i.succ.castSucc) \
        TreeSequenceVertexSet (HierarchyStarredStage H i.castSucc)).biUnion
          fun v => MissingColors G phi v)) :
    BoundaryColorEdges G phi
      (TreeSequenceVertexSet (H.stage i.succ.castSucc)) alpha = ∅ := by
-- BODY
  sorry
