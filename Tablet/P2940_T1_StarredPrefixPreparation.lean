import Tablet.CertifiedETTPredecessor
import Tablet.ColoredVertexSetClosed
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ElementaryClosedMissingColorOdd
import Tablet.GoodHierarchyElementaryLarge
import Tablet.GoodHierarchyPrefixRepackage
import Tablet.HierarchyStoredColorsCardinality
import Tablet.HierarchyStoredColorsAntitone
import Tablet.HierarchyTerminalStoredColorsSubsetLast
import Tablet.MissingColorsNonemptyOfMaximumDegree
import Tablet.MaximumDefectiveChoice
import Tablet.ParallelClosureUnionElementary
import Tablet.ParallelCommonMissingClosed
import Tablet.TechnicalInductionContext
import Tablet.TechnicalTheoremBase
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TreeIncidentEdge
import Tablet.OrderedTreeUnion
import Tablet.sc2

-- [TABLET NODE: P2940_T1_StarredPrefixPreparation]
theorem P2940_T1_StarredPrefixPreparation
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (ctx : TechnicalInductionContext G k e0 ett.rounds)
    (hMP : MaximumProperty ett) (base : HierarchyBase ett phi)
    (hdegree : MaximumDegree G + 1 <= k)
    (hlargeOrder : 11 <= TashkinovOrder G)
    (hmissingBound : forall {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (current : ExtendedTashkinovTree G k e0 input' T' generating'),
      current.rounds = ett.rounds -> MaximumProperty current ->
      forall (base' : HierarchyBase current generating')
        (K : TashkinovHierarchy current base'), GoodHierarchy K ->
        let n : Fin (current.rounds + 1) := Fin.last current.rounds
        let Tn := current.series.data.tree n.castSucc
        2 * current.rounds + 11 <= (TreeMissingColors generating' Tn).card)
    (U : TreeSequence G e0)
    (corrU : CorrespondingExtendedTashkinovTree G k e0 ett phi U)
    (hMPU : MaximumProperty corrU.replacementETT)
    (baseU : HierarchyBase corrU.replacementETT phi)
    (hcore : baseU.core = base.core)
    (H : TashkinovHierarchy corrU.replacementETT baseU)
    (good : GoodHierarchy H)
    (hstrict :
      (ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE -> base.core.length < U.length) /\
      (Not (ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE) ->
        (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < U.length)) :
    let lastH : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let A := HierarchyStarredStage H lastH
    IsProperEdgeColoring G phi /\ IsOneEdgeUncolored phi e0 /\
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet A) /\
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet U) /\
    TreeSequenceInitialSegment A U /\ A.length < U.length /\
    Odd (TreeSequenceVertexSet A).card /\
    ((HierarchyTerminalStoredColors H).biUnion (good.gamma lastH)).card <
      (TreeMissingColors phi U).card := by
-- BODY
  sorry
