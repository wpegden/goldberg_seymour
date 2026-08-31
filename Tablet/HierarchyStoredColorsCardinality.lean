import Tablet.HierarchyStoredColorsAt
import Tablet.TashkinovStoredColorsCardinality

-- [TABLET NODE: HierarchyStoredColorsCardinality]
theorem HierarchyStoredColorsCardinality {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T generating}
    {base : HierarchyBase ett phi} (H : TashkinovHierarchy ett base)
    (j : Fin (H.dividerCount + 1)) :
    (HierarchyStoredColorsAt H j).card ≤ ett.rounds := by
-- BODY
  classical
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  have hsub : HierarchyStoredColorsAt H j ⊆
      TashkinovStoredColors ett.series.data n := by
    intro c hc
    unfold HierarchyStoredColorsAt at hc
    exact (Finset.mem_sdiff.mp hc).1
  calc
    (HierarchyStoredColorsAt H j).card ≤
        (TashkinovStoredColors ett.series.data n).card :=
      Finset.card_le_card hsub
    _ ≤ n.val := TashkinovStoredColorsCardinality G k ett.rounds e0 input
      ett.series n
    _ = ett.rounds := by simp [n]
