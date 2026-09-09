import Tablet.AlgorithmFiveFiveSeed
import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.GoodHierarchyInitialPairsNonPE
import Tablet.GoodHierarchyInitialPairsPE
import Tablet.GoodHierarchyRestrictedAugmentation
import Tablet.HierarchyBase
import Tablet.HierarchySegmentColors
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyTerminalStoredColors
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumProperty
import Tablet.ModColoring
import Tablet.RevisitingExtensionCertificate
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeColorSetClosed
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TwoColorCycle
import Tablet.sc2

-- [TABLET NODE: AlgorithmFiveFiveBaseStage]
theorem AlgorithmFiveFiveBaseStage {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hMP : MaximumProperty ett) (hmod : ModColoring ett phi)
    (base : HierarchyBase ett phi)
    (hcoreStrict :
      ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE →
        (ett.series.data.tree (Fin.last ett.rounds).castSucc).length <
          base.core.length)
    (hcoreClosure :
      ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE →
        TashkinovClosure phi base.core
          (ett.series.data.tree (Fin.last (ett.rounds + 1))))
    (hlarge : 2 * ett.rounds + 11 ≤
      (TreeMissingColors phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).card)
    (hparallelFacts :
      ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE →
        (∃ alpha : Fin k,
          alpha ∈ TreeMissingColors phi base.core ∧
            ¬ TreeColorSetClosed G phi base.core {alpha}) ∧
        TreeColorSetClosed G phi base.core
          (TreeMissingColors phi
              (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∩
            TreeMissingColors phi base.closure) ∧
        4 ≤ (TreeMissingColors phi
              (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∩
            TreeMissingColors phi base.closure).card) :
    ∃ (J U : TreeSequence G e0)
        (corrU : CorrespondingExtendedTashkinovTree G k e0 ett phi U),
      (((ett.series.data.kind (Fin.last ett.rounds) =
            some TashkinovExtensionKind.PE ∧ J = base.core) ∨
        ((ett.series.data.kind (Fin.last ett.rounds) =
              some TashkinovExtensionKind.SE ∨
            ett.series.data.kind (Fin.last ett.rounds) =
              some TashkinovExtensionKind.RE) ∧
          ∃ f : E,
            ett.series.data.connectingEdges (Fin.last ett.rounds) = {f} ∧
            TreeSequenceAdjoinEdge
              (ett.series.data.tree (Fin.last ett.rounds).castSucc) f J)) ∧
      TashkinovAugmentationSequence phi J U ∧
      TreeSequenceInitialSegment J U ∧
      (ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE → base.core.length < U.length) ∧
      (ett.series.data.kind (Fin.last ett.rounds) ≠
          some TashkinovExtensionKind.PE →
        (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < U.length) ∧
      MaximumProperty corrU.replacementETT ∧
      ∃ baseU : HierarchyBase corrU.replacementETT phi,
        baseU.core = base.core ∧
        baseU.closure = base.closure ∧
        baseU.supportPosition.val = base.supportPosition.val ∧
        ∃ KU : TashkinovHierarchy corrU.replacementETT baseU,
          KU.dividerCount = 0 ∧
          KU.stage 0 =
            ett.series.data.tree (Fin.last ett.rounds).castSucc ∧
          KU.stage (Fin.last (KU.dividerCount + 1)) = U ∧
          ∃ goodU : GoodHierarchy KU, (
            (∀ eta : Fin k,
              eta ∈ HierarchyStoredColorsAt KU
                  (Fin.last KU.dividerCount) →
                (goodU.gamma (Fin.last KU.dividerCount) eta).card = 2 ∧
                goodU.gamma (Fin.last KU.dividerCount) eta ⊆
                  TreeMissingColors phi
                      (ett.series.data.tree
                        (Fin.last ett.rounds).castSucc) \
                    HierarchySegmentColors KU
                      (Fin.last KU.dividerCount) eta) ∧
            (∀ eta theta : Fin k,
              eta ∈ HierarchyStoredColorsAt KU
                  (Fin.last KU.dividerCount) →
              theta ∈ HierarchyStoredColorsAt KU
                  (Fin.last KU.dividerCount) → eta ≠ theta →
                Disjoint
                  (goodU.gamma (Fin.last KU.dividerCount) eta)
                  (goodU.gamma (Fin.last KU.dividerCount) theta)) ∧
            (ett.series.data.kind (Fin.last ett.rounds) =
                some TashkinovExtensionKind.PE →
              ¬ TreeColorSetMinusClosed G phi base.core
                ((HierarchyStoredColorsAt KU
                    (Fin.last KU.dividerCount)).biUnion
                  (goodU.gamma (Fin.last KU.dividerCount))) ∧
              4 ≤ ((TreeMissingColors phi
                    (ett.series.data.tree
                      (Fin.last ett.rounds).castSucc) ∩
                  TreeMissingColors phi base.closure) \
                (HierarchyStoredColorsAt KU
                    (Fin.last KU.dividerCount)).biUnion
                  (goodU.gamma (Fin.last KU.dividerCount))).card)) ∧
            TreeColorSetMinusClosed G phi U
              ((HierarchyTerminalStoredColors KU).biUnion
                (goodU.gamma (Fin.last KU.dividerCount)))) := by
-- BODY
  sorry
