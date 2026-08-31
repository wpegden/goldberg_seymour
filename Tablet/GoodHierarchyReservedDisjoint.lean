import Tablet.GoodHierarchy

-- [TABLET NODE: GoodHierarchyReservedDisjoint]
theorem GoodHierarchyReservedDisjoint {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T generating}
    {base : HierarchyBase ett phi} {H : TashkinovHierarchy ett base}
    (good : GoodHierarchy H) (j : Fin (H.dividerCount + 1)) :
    (∀ eta ∈ HierarchyStoredColorsAt H j,
      good.gamma j eta ⊆
        TreeMissingColors phi (HierarchyStarredStage H j)) ∧
    Disjoint
      ((HierarchyStoredColorsAt H j).biUnion (good.gamma j))
      (HierarchyStoredColorsAt H j) := by
-- BODY
  sorry
