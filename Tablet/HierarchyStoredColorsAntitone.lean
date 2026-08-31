import Tablet.HierarchyStoredColorsAt

-- [TABLET NODE: HierarchyStoredColorsAntitone]
theorem HierarchyStoredColorsAntitone {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T generating}
    {base : HierarchyBase ett phi} (H : TashkinovHierarchy ett base)
    (i : Fin H.dividerCount) :
    HierarchyStoredColorsAt H i.succ ⊆
      HierarchyStoredColorsAt H i.castSucc := by
-- BODY
  sorry
