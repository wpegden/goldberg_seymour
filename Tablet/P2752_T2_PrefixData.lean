import Tablet.GoodHierarchyTerminalPrefixRepackage
import Tablet.HierarchyCounterexample
import Tablet.HierarchyLEMStable

-- [TABLET NODE: P2752_T2_PrefixData]
structure P2752_T2_PrefixData {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T phi}
    {base : HierarchyBase ett phi} (C : HierarchyCounterexample base)
    (Bplus : TreeSequence G e0) (sigma : PartialEdgeColoring E k) where
-- BODY
  belowFull : TreeSequenceInitialSegment Bplus T
  penultimateLength : T.length = Bplus.length + 1
  ladderBelow : TreeSequenceInitialSegment
    (ett.series.data.tree (Fin.last ett.rounds).castSucc) Bplus
  oldETT : ExtendedTashkinovTree G k e0 input Bplus phi
  oldMaximum : MaximumProperty oldETT
  oldRung : oldETT.rounds = ett.rounds
  oldSeries : HEq oldETT.series ett.series
  oldBase : HierarchyBase oldETT phi
  oldCore : oldBase.core = base.core
  oldClosure : oldBase.closure = base.closure
  oldSupport : oldBase.supportPosition.val = base.supportPosition.val
  oldHierarchy : TashkinovHierarchy oldETT oldBase
  oldCount : oldHierarchy.dividerCount = C.hierarchy.dividerCount
  oldStages : ∀ j : Fin (oldHierarchy.dividerCount + 1),
    let jo := Fin.cast (congrArg (fun n : ℕ => n + 1) oldCount) j
    oldHierarchy.stage j.castSucc = C.hierarchy.stage jo.castSucc ∧
      HierarchyStarredStage oldHierarchy j = HierarchyStarredStage C.hierarchy jo
  oldDividers : ∀ i : Fin oldHierarchy.dividerCount,
    (oldHierarchy.dividerPosition i).val =
      (C.hierarchy.dividerPosition (Fin.cast oldCount i)).val
  oldGood : GoodHierarchy oldHierarchy
  oldColors : ∀ j : Fin (oldHierarchy.dividerCount + 1),
    let jo := Fin.cast (congrArg (fun n : ℕ => n + 1) oldCount) j
    HierarchyStoredColorsAt oldHierarchy j = HierarchyStoredColorsAt C.hierarchy jo ∧
      HierarchyStageMissingColors oldHierarchy j =
        HierarchyStageMissingColors C.hierarchy jo ∧
      ∀ eta : Fin k, oldGood.gamma j eta = C.good.gamma jo eta ∧
        HierarchySegmentColors oldHierarchy j eta ⊆
          HierarchySegmentColors C.hierarchy jo eta
  proper : IsProperEdgeColoring G sigma
  oneUncolored : IsOneEdgeUncolored sigma e0
  invariant : TreeColoringInvariant Bplus phi sigma
  incidentFixed : ∀ f : E, TreeIncidentEdge Bplus f → sigma f = phi f
  corresponding : CorrespondingExtendedTashkinovTree G k e0 oldETT sigma Bplus
  maximum : MaximumProperty corresponding.replacementETT
  newBase : HierarchyBase corresponding.replacementETT sigma
  newHierarchy : TashkinovHierarchy corresponding.replacementETT newBase
  newGood : GoodHierarchy newHierarchy
  sameGood : SameGoodHierarchy oldGood newGood
