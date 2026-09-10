import Tablet.AlgorithmFiveFiveBaseStage
import Tablet.BoundaryColorEdges
import Tablet.CertifiedETTPredecessor
import Tablet.ColoredVertexSetElementary
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.CorrespondingExtendedTashkinovTreeTransTrees
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyBase
import Tablet.HierarchyBaseCorrespondingTransport
import Tablet.HierarchySegmentColors
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyTerminalStoredColors
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDegree
import Tablet.MaximumProperty
import Tablet.MaximumPropertyTransport
import Tablet.ModColoring
import Tablet.ParallelBaseFourCommonMissingColors
import Tablet.ParallelClosureUnionElementary
import Tablet.ParallelCommonMissingClosed
import Tablet.ParallelCoreAugmentationStrict
import Tablet.StableColoring
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceInitialSegment
import Tablet.TashkinovAugmentationSequenceStrictBoundaryWitness
import Tablet.TashkinovClosure
import Tablet.TashkinovClosureExists
import Tablet.TashkinovClosureVertexSetUnique
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.Td
import Tablet.TechnicalInductionContext
import Tablet.TechnicalTheoremBase
import Tablet.TreeColorSetClosed
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceInitialSegmentVertexSetEq
import Tablet.TreeSequenceVertexSet
import Tablet.sc2

-- [TABLET NODE: ParallelSpecialClosurePreparation]
theorem ParallelSpecialClosurePreparation
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (ctx : TechnicalInductionContext G k e0 ett.rounds)
    (hMP : MaximumProperty ett)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (base : HierarchyBase ett phi)
    (hdegree : MaximumDegree G + 1 <= k)
    (hlarge : 2 * ett.rounds + 11 <=
      (TreeMissingColors phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).card) :
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
    TashkinovAugmentationSequence phi Tn base.core /\
      Tn.length < base.core.length /\
      (ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) ∨
        exists (U : TreeSequence G e0)
            (corrU : CorrespondingExtendedTashkinovTree G k e0 ett phi U),
          MaximumProperty corrU.replacementETT /\
            TashkinovAugmentationSequence phi base.core U /\
            TreeSequenceInitialSegment base.core U /\
            base.core.length < U.length /\
            exists baseU : HierarchyBase corrU.replacementETT phi,
              baseU.core = base.core /\
                baseU.closure = base.closure /\
                baseU.supportPosition.val = base.supportPosition.val /\
                exists KU : TashkinovHierarchy corrU.replacementETT baseU,
                  KU.dividerCount = 0 /\
                    KU.stage 0 = Tn /\
                    KU.stage (Fin.last (KU.dividerCount + 1)) = U /\
                    exists goodU : GoodHierarchy KU,
                      (forall eta : Fin k,
                        eta ∈ HierarchyStoredColorsAt KU
                            (Fin.last KU.dividerCount) ->
                          (goodU.gamma
                              (Fin.last KU.dividerCount) eta).card = 2 /\
                            goodU.gamma
                                (Fin.last KU.dividerCount) eta ⊆
                              TreeMissingColors phi Tn \
                                HierarchySegmentColors KU
                                  (Fin.last KU.dividerCount) eta) /\
                      (forall eta theta : Fin k,
                        eta ∈ HierarchyStoredColorsAt KU
                            (Fin.last KU.dividerCount) ->
                        theta ∈ HierarchyStoredColorsAt KU
                            (Fin.last KU.dividerCount) ->
                        eta ≠ theta ->
                          Disjoint
                            (goodU.gamma
                              (Fin.last KU.dividerCount) eta)
                            (goodU.gamma
                              (Fin.last KU.dividerCount) theta)) /\
                      (¬ TreeColorSetMinusClosed G phi base.core
                        ((HierarchyStoredColorsAt KU
                            (Fin.last KU.dividerCount)).biUnion
                          (goodU.gamma (Fin.last KU.dividerCount)))) /\
                      4 <= ((TreeMissingColors phi Tn ∩
                            TreeMissingColors phi base.closure) \
                          (HierarchyStoredColorsAt KU
                            (Fin.last KU.dividerCount)).biUnion
                            (goodU.gamma
                              (Fin.last KU.dividerCount))).card /\
                      TreeColorSetMinusClosed G phi U
                        ((HierarchyTerminalStoredColors KU).biUnion
                          (goodU.gamma (Fin.last KU.dividerCount)))) := by
-- BODY
  sorry
