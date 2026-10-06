import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceInitialSegment
import Tablet.TashkinovHierarchy
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequencePrefix

-- [TABLET NODE: GoodHierarchySameDividerReconstruction]
theorem GoodHierarchySameDividerReconstruction {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (J U : TreeSequence G e0)
    (corrJ : CorrespondingExtendedTashkinovTree G k e0 ett sigma J)
    (baseJ : HierarchyBase corrJ.replacementETT sigma)
    (KJ : TashkinovHierarchy corrJ.replacementETT baseJ)
    (corrU : CorrespondingExtendedTashkinovTree G k e0 ett sigma U)
    (baseU : HierarchyBase corrU.replacementETT sigma)
    (hcore : baseU.core = baseJ.core)
    (hJU : TashkinovAugmentationSequence sigma J U) :
    ∃ KU : TashkinovHierarchy corrU.replacementETT baseU,
      ∃ hcount : KU.dividerCount = KJ.dividerCount,
        (∀ j : Fin (KU.dividerCount + 1),
          let jo : Fin (KJ.dividerCount + 1) :=
            Fin.cast (congrArg (fun n : ℕ => n + 1) hcount) j
          KU.stage j.castSucc = KJ.stage jo.castSucc ∧
            HierarchyStarredStage KU j = HierarchyStarredStage KJ jo ∧
            HierarchyStoredColorsAt KU j =
              HierarchyStoredColorsAt KJ jo ∧
            HierarchyStageMissingColors KU j =
              HierarchyStageMissingColors KJ jo) ∧
        (∀ i : Fin KU.dividerCount,
          (KU.dividerPosition i).val =
            (KJ.dividerPosition (Fin.cast hcount i)).val) := by
-- BODY
  sorry
