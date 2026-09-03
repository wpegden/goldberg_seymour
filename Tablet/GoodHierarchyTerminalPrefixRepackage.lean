import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyBase
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchySegmentColors
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.MaximumProperty
import Tablet.MissingColors
import Tablet.OrderedTreeUnion
import Tablet.TashkinovHierarchy
import Tablet.TreeSequenceInitialSegment

-- [TABLET NODE: GoodHierarchyTerminalPrefixRepackage]
theorem GoodHierarchyTerminalPrefixRepackage {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett)
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base)
    (good : GoodHierarchy H)
    (B : TreeSequence G e0)
    (hAB : TreeSequenceInitialSegment
      (HierarchyStarredStage H (Fin.last H.dividerCount)) B)
    (hABstrict :
      (HierarchyStarredStage H (Fin.last H.dividerCount)).length < B.length)
    (hBT : TreeSequenceInitialSegment B T) :
    ∃ ettB : ExtendedTashkinovTree G k e0 input B generating,
      MaximumProperty ettB ∧
      ettB.rounds = ett.rounds ∧ HEq ettB.series ett.series ∧
      ∃ baseB : HierarchyBase ettB phi,
        baseB.core = base.core ∧
        baseB.closure = base.closure ∧
        baseB.supportPosition.val = base.supportPosition.val ∧
        ∃ HB : TashkinovHierarchy ettB baseB,
          ∃ hcount : HB.dividerCount = H.dividerCount,
            (∀ j : Fin (HB.dividerCount + 1),
              let jo : Fin (H.dividerCount + 1) :=
                Fin.cast (congrArg (fun n : ℕ => n + 1) hcount) j
              HB.stage j.castSucc = H.stage jo.castSucc ∧
                HierarchyStarredStage HB j = HierarchyStarredStage H jo) ∧
            (∀ i : Fin HB.dividerCount,
              (HB.dividerPosition i).val =
                (H.dividerPosition (Fin.cast hcount i)).val) ∧
            ∃ goodB : GoodHierarchy HB,
              ∀ j : Fin (HB.dividerCount + 1),
                let jo : Fin (H.dividerCount + 1) :=
                  Fin.cast (congrArg (fun n : ℕ => n + 1) hcount) j
                HierarchyStoredColorsAt HB j = HierarchyStoredColorsAt H jo ∧
                  HierarchyStageMissingColors HB j =
                    HierarchyStageMissingColors H jo ∧
                  ∀ eta : Fin k,
                    goodB.gamma j eta = good.gamma jo eta ∧
                      HierarchySegmentColors HB j eta ⊆
                        HierarchySegmentColors H jo eta := by
-- BODY
  sorry
