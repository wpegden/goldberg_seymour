import Tablet.BoundaryMissingColorAugmentation
import Tablet.BoundaryColorEdges
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyBaseCorrespondingTransport
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyFirstMissingPositionPrefixCutoff
import Tablet.HierarchySegmentColors
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyTerminalStoredColors
import Tablet.MaximumDefectiveChoice
import Tablet.StableColoring
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceInitialSegment
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeColorSetClosed
import Tablet.TreeMissingColors
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.sc2

-- [TABLET NODE: GoodHierarchyRestrictedEndpointReconstruction]
theorem GoodHierarchyRestrictedEndpointReconstruction {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (J U : TreeSequence G e0)
    (corrJ : CorrespondingExtendedTashkinovTree G k e0 ett sigma J)
    (baseJ : HierarchyBase corrJ.replacementETT sigma)
    (KJ : TashkinovHierarchy corrJ.replacementETT baseJ)
    (goodJ : GoodHierarchy KJ)
    (corrU : CorrespondingExtendedTashkinovTree G k e0 ett sigma U)
    (hJU : TashkinovAugmentationSequence sigma J U) :
    let lastJ : Fin (KJ.dividerCount + 1) := Fin.last KJ.dividerCount
    let A : TreeSequence G e0 := HierarchyStarredStage KJ lastJ
    let restrictedColors : TreeSequence G e0 → Fin k → Finset (Fin k) :=
      fun W eta => Finset.univ.filter fun c =>
        ∃ r : Fin W.length, A.length ≤ r.val ∧
          r.val < min (HierarchyFirstMissingPosition sigma W eta).val W.length ∧
          sigma (W.edge r) = some c
    (∀ eta : Fin k, eta ∈ HierarchyStoredColorsAt KJ lastJ →
      Disjoint (goodJ.gamma lastJ eta) (restrictedColors U eta)) →
    (∀ W : TreeSequence G e0,
      TashkinovAugmentation sigma U W →
      (∀ eta : Fin k, eta ∈ HierarchyStoredColorsAt KJ lastJ →
        Disjoint (goodJ.gamma lastJ eta) (restrictedColors W eta)) →
      False) →
    ∃ baseU : HierarchyBase corrU.replacementETT sigma,
      baseU.core = baseJ.core ∧
      baseU.closure = baseJ.closure ∧
      baseU.supportPosition.val = baseJ.supportPosition.val ∧
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
              (KJ.dividerPosition (Fin.cast hcount i)).val) ∧
          ∃ goodU : GoodHierarchy KU,
            (∀ j : Fin (KU.dividerCount + 1),
              let jo : Fin (KJ.dividerCount + 1) :=
                Fin.cast (congrArg (fun n : ℕ => n + 1) hcount) j
              ∀ eta : Fin k,
                goodU.gamma j eta = goodJ.gamma jo eta) ∧
            HierarchyTerminalStoredColors KU ⊆
              HierarchyStoredColorsAt KJ lastJ ∧
            TreeColorSetMinusClosed G sigma U
              ((HierarchyTerminalStoredColors KU).biUnion
                (goodU.gamma (Fin.last KU.dividerCount))) := by
-- BODY
  sorry
