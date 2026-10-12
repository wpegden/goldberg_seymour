import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.GoodHierarchyReservedDisjoint
import Tablet.HierarchyFirstMissingPositionPrefixCutoff
import Tablet.HierarchyTerminalStoredColorsSubsetLast
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.ColoredVertexSetElementary

-- [TABLET NODE: P2940_T1_OneDividerRefresh]
theorem P2940_T1_OneDividerRefresh
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (U W : TreeSequence G e0)
    (corrU : CorrespondingExtendedTashkinovTree G k e0 ett phi U)
    (corrW : CorrespondingExtendedTashkinovTree G k e0 ett phi W)
    (baseU : HierarchyBase corrU.replacementETT phi)
    (baseW : HierarchyBase corrW.replacementETT phi)
    (hcore : baseW.core = baseU.core)
    (hclosure : baseW.closure = baseU.closure)
    (H : TashkinovHierarchy corrU.replacementETT baseU)
    (good : GoodHierarchy H)
    (helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet U))
    (eta beta gammaOne gammaTwo : Fin k) (f : E)
    (heta : eta ∈ HierarchyTerminalStoredColors H)
    (hbeta : beta ∈ good.gamma (Fin.last H.dividerCount) eta)
    (hfc : phi f = some beta) (hadjoin : TreeSequenceAdjoinEdge U f W)
    (hne : gammaOne ≠ gammaTwo)
    (hg1 : gammaOne ∈ (TreeSequenceVertexSet U \ TreeSequenceVertexSet
      (HierarchyStarredStage H (Fin.last H.dividerCount))).biUnion
        (MissingColors G phi))
    (hg2 : gammaTwo ∈ (TreeSequenceVertexSet U \ TreeSequenceVertexSet
      (HierarchyStarredStage H (Fin.last H.dividerCount))).biUnion
        (MissingColors G phi))
    (hfresh : Disjoint {gammaOne, gammaTwo}
      ((HierarchyTerminalStoredColors H).biUnion
        (good.gamma (Fin.last H.dividerCount))))
    (hminus : TreeColorSetMinusClosed G phi U
      ((HierarchyTerminalStoredColors H).biUnion
        (good.gamma (Fin.last H.dividerCount)))) :
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
          (forall j : Fin (H.dividerCount + 1), forall theta : Fin k,
            goodW.gamma (Fin.castLE (by omega) j) theta = good.gamma j theta) /\
          goodW.gamma (Fin.last HW.dividerCount) eta = {gammaOne, gammaTwo} /\
          (forall theta : Fin k, theta ∈ HierarchyTerminalStoredColors H ->
            theta ≠ eta -> goodW.gamma (Fin.last HW.dividerCount) theta =
              good.gamma (Fin.last H.dividerCount) theta) := by
-- BODY
  sorry
