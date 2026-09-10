import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.CertifiedETTPredecessor
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.Degree
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.GoodHierarchyElementaryLarge
import Tablet.GoodHierarchyPrefixRepackage
import Tablet.GoodHierarchyReservedDisjoint
import Tablet.GoodHierarchyRestrictedAugmentation
import Tablet.HierarchyBase
import Tablet.HierarchyBaseCorrespondingTransport
import Tablet.HierarchySegmentColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyTerminalStoredColors
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDegree
import Tablet.MaximumProperty
import Tablet.MaximumPropertyTransport
import Tablet.MissingColors
import Tablet.ModColoring
import Tablet.ParallelClosureUnionElementary
import Tablet.ParallelCommonMissingClosed
import Tablet.PresentColors
import Tablet.StableColoring
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceInitialSegment
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovHierarchy
import Tablet.TashkinovOrder
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TashkinovStoredColorsCardinality
import Tablet.TechnicalInductionContext
import Tablet.TechnicalTheoremBase
import Tablet.TreeColorSetClosed
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.sc2

-- [TABLET NODE: AlgorithmFiveSixFixedRootRefresh]
theorem AlgorithmFiveSixFixedRootRefresh
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (ctx : TechnicalInductionContext G k e0 ett.rounds)
    (hMP : MaximumProperty ett)
    (base : HierarchyBase ett phi)
    (hdegree : MaximumDegree G + 1 <= k)
    (hlargeOrder : 11 <= TashkinovOrder G)
    (hmissingBound : forall {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (current : ExtendedTashkinovTree G k e0 input' T' generating'),
      current.rounds = ett.rounds -> MaximumProperty current ->
      forall (base' : HierarchyBase current generating')
        (K : TashkinovHierarchy current base'),
        GoodHierarchy K ->
        let n : Fin (current.rounds + 1) := Fin.last current.rounds
        let Tn := current.series.data.tree n.castSucc
        2 * current.rounds + 11 <=
          (TreeMissingColors generating' Tn).card)
    (U : TreeSequence G e0)
    (corrU : CorrespondingExtendedTashkinovTree G k e0 ett phi U)
    (hMPU : MaximumProperty corrU.replacementETT)
    (baseU : HierarchyBase corrU.replacementETT phi)
    (hbaseCore : baseU.core = base.core)
    (hbaseClosure : baseU.closure = base.closure)
    (hbaseSupport : baseU.supportPosition.val = base.supportPosition.val)
    (H : TashkinovHierarchy corrU.replacementETT baseU)
    (good : GoodHierarchy H)
    (hminus : TreeColorSetMinusClosed G phi U
      ((HierarchyTerminalStoredColors H).biUnion
        (good.gamma (Fin.last H.dividerCount))))
    (hnotClosed : ¬ TreeColorSetClosed G phi U (TreeMissingColors phi U))
    (J : TreeSequence G e0)
    (hanchor :
      (ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE /\ J = base.core /\
        TashkinovAugmentationSequence phi
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) J) \/
      ((ett.series.data.kind (Fin.last ett.rounds) =
            some TashkinovExtensionKind.SE \/
          ett.series.data.kind (Fin.last ett.rounds) =
            some TashkinovExtensionKind.RE) /\
        exists f0 : E,
          ett.series.data.connectingEdges (Fin.last ett.rounds) = {f0} /\
          TreeSequenceAdjoinEdge
            (ett.series.data.tree (Fin.last ett.rounds).castSucc) f0 J))
    (hanchorStrict :
      (ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE -> base.core.length < U.length) /\
      (ett.series.data.kind (Fin.last ett.rounds) !=
          some TashkinovExtensionKind.PE ->
        (ett.series.data.tree
          (Fin.last ett.rounds).castSucc).length < U.length))
    (hroute : TashkinovAugmentationSequence phi J U) :
    let lastH : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let A : TreeSequence G e0 := HierarchyStarredStage H lastH
    let oldReserved : Finset (Fin k) :=
      (HierarchyTerminalStoredColors H).biUnion (good.gamma lastH)
    exists (alpha beta eta gammaOne gammaTwo : Fin k) (f : E)
        (W : TreeSequence G e0),
      ColoredVertexSetElementary G phi (TreeSequenceVertexSet A) /\
      ColoredVertexSetElementary G phi (TreeSequenceVertexSet U) /\
      A.length < U.length /\
      Odd (TreeSequenceVertexSet A).card /\
      Odd (TreeSequenceVertexSet U).card /\
      alpha ∈ TreeMissingColors phi U \ oldReserved /\
      TreeColorSetClosed G phi U {alpha} /\
      beta ∈ TreeMissingColors phi U /\
      beta ∈ oldReserved /\
      eta ∈ HierarchyTerminalStoredColors H /\
      beta ∈ good.gamma lastH eta /\
      (forall theta : Fin k, theta ∈ HierarchyTerminalStoredColors H ->
        beta ∈ good.gamma lastH theta -> theta = eta) /\
      f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet U) beta /\
      phi f = some beta /\
      TreeSequenceAdjoinEdge U f W /\
      TashkinovAugmentation phi U W /\
      gammaOne != gammaTwo /\
      gammaOne ∈
        (TreeSequenceVertexSet U \ TreeSequenceVertexSet A).biUnion
          (MissingColors G phi) /\
      gammaTwo ∈
        (TreeSequenceVertexSet U \ TreeSequenceVertexSet A).biUnion
          (MissingColors G phi) /\
      Disjoint {gammaOne, gammaTwo} oldReserved /\
      beta ∉ ({gammaOne, gammaTwo} : Finset (Fin k)) /\
      exists
          (corrW : CorrespondingExtendedTashkinovTree G k e0 ett phi W),
        MaximumProperty corrW.replacementETT /\
        TashkinovAugmentationSequence phi J W /\
        exists baseW : HierarchyBase corrW.replacementETT phi,
          baseW.core = base.core /\
          baseW.closure = base.closure /\
          baseW.supportPosition.val = base.supportPosition.val /\
          exists HW : TashkinovHierarchy corrW.replacementETT baseW,
            exists hcountW : HW.dividerCount = H.dividerCount + 1,
              (forall j : Fin (H.dividerCount + 2),
                HW.stage (Fin.castLE (by omega) j) = H.stage j) /\
              HW.stage (Fin.last HW.dividerCount).castSucc = U /\
              HierarchyStarredStage HW (Fin.last HW.dividerCount) = U /\
              HW.stage (Fin.last HW.dividerCount).succ = W /\
              (forall i : Fin H.dividerCount,
                (HW.dividerPosition (Fin.castLE (by omega) i)).val =
                  (H.dividerPosition i).val) /\
              (HW.dividerPosition (Fin.cast hcountW.symm
                (Fin.last H.dividerCount))).val = U.length /\
              (forall j : Fin (H.dividerCount + 1),
                HierarchyStoredColorsAt HW (Fin.castLE (by omega) j) =
                  HierarchyStoredColorsAt H j) /\
              HierarchyStoredColorsAt HW (Fin.last HW.dividerCount) =
                HierarchyTerminalStoredColors H /\
              exists goodW : GoodHierarchy HW,
                (forall j : Fin (H.dividerCount + 1),
                  forall theta : Fin k,
                    goodW.gamma (Fin.castLE (by omega) j) theta =
                      good.gamma j theta) /\
                goodW.gamma (Fin.last HW.dividerCount) eta =
                  {gammaOne, gammaTwo} /\
                (forall theta : Fin k,
                  theta ∈ HierarchyTerminalStoredColors H -> theta != eta ->
                    goodW.gamma (Fin.last HW.dividerCount) theta =
                      good.gamma lastH theta) /\
                exists (V' : TreeSequence G e0)
                    (corrV : CorrespondingExtendedTashkinovTree
                      G k e0 ett phi V'),
                  MaximumProperty corrV.replacementETT /\
                  U.length < V'.length /\
                  TashkinovAugmentationSequence phi J V' /\
                  exists baseV : HierarchyBase corrV.replacementETT phi,
                    baseV.core = base.core /\
                    baseV.closure = base.closure /\
                    baseV.supportPosition.val = base.supportPosition.val /\
                    exists K : TashkinovHierarchy corrV.replacementETT baseV,
                      exists hcountV : K.dividerCount = H.dividerCount + 1,
                        (forall j : Fin (H.dividerCount + 2),
                          K.stage (Fin.castLE (by omega) j) = H.stage j) /\
                        K.stage (Fin.last K.dividerCount).castSucc = U /\
                        HierarchyStarredStage K
                          (Fin.last K.dividerCount) = U /\
                        K.stage (Fin.last K.dividerCount).succ = V' /\
                        (forall i : Fin H.dividerCount,
                          (K.dividerPosition
                            (Fin.castLE (by omega) i)).val =
                              (H.dividerPosition i).val) /\
                        (K.dividerPosition (Fin.cast hcountV.symm
                          (Fin.last H.dividerCount))).val = U.length /\
                        (forall j : Fin (H.dividerCount + 1),
                          HierarchyStoredColorsAt K
                              (Fin.castLE (by omega) j) =
                            HierarchyStoredColorsAt H j) /\
                        HierarchyStoredColorsAt K
                            (Fin.last K.dividerCount) =
                          HierarchyTerminalStoredColors H /\
                        exists goodV : GoodHierarchy K,
                          (forall j : Fin (H.dividerCount + 1),
                            forall theta : Fin k,
                              goodV.gamma (Fin.castLE (by omega) j) theta =
                                good.gamma j theta) /\
                          goodV.gamma (Fin.last K.dividerCount) eta =
                            {gammaOne, gammaTwo} /\
                          (forall theta : Fin k,
                            theta ∈ HierarchyTerminalStoredColors H ->
                            theta != eta ->
                              goodV.gamma (Fin.last K.dividerCount) theta =
                                good.gamma lastH theta) /\
                          TreeColorSetMinusClosed G phi V'
                            ((HierarchyTerminalStoredColors K).biUnion
                              (goodV.gamma
                                (Fin.last K.dividerCount))) := by
-- BODY
  sorry
