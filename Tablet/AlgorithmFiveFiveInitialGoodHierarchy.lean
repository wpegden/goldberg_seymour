import Tablet.AlgorithmFiveFiveSeed
import Tablet.ColoredVertexSetClosed
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.GoodHierarchyInitialPairsNonPE
import Tablet.GoodHierarchyInitialPairsPE
import Tablet.HierarchyBase
import Tablet.HierarchySegmentColors
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.MaximumDefectiveChoice
import Tablet.RevisitingExtensionCertificate
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeColorSetClosed
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeMissingColors
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TwoColorCycle
import Tablet.sc2

-- [TABLET NODE: AlgorithmFiveFiveInitialGoodHierarchy]
theorem AlgorithmFiveFiveInitialGoodHierarchy {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (J : TreeSequence G e0)
    (corrJ : CorrespondingExtendedTashkinovTree G k e0 ett phi J)
    (baseJ : HierarchyBase corrJ.replacementETT phi)
    (KJ : TashkinovHierarchy corrJ.replacementETT baseJ)
    (hbaseCore : baseJ.core = base.core)
    (hbaseClosure : baseJ.closure = base.closure)
    (hzero : KJ.dividerCount = 0)
    (hstageZero : KJ.stage 0 =
      ett.series.data.tree (Fin.last ett.rounds).castSucc)
    (hseed :
      ((ett.series.data.kind (Fin.last ett.rounds) =
            some TashkinovExtensionKind.PE ∧ J = base.core) ∨
        ((ett.series.data.kind (Fin.last ett.rounds) =
              some TashkinovExtensionKind.SE ∨
            ett.series.data.kind (Fin.last ett.rounds) =
              some TashkinovExtensionKind.RE) ∧
          ∃ f : E,
            ett.series.data.connectingEdges (Fin.last ett.rounds) = {f} ∧
            TreeSequenceAdjoinEdge
              (ett.series.data.tree (Fin.last ett.rounds).castSucc) f J)))
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
    ∃ goodJ : GoodHierarchy KJ,
      HierarchyStageMissingColors KJ (Fin.last KJ.dividerCount) =
        TreeMissingColors phi
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∧
      (ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE →
        ¬ TreeColorSetMinusClosed G phi base.core
            ((HierarchyStoredColorsAt KJ
              (Fin.last KJ.dividerCount)).biUnion
                (goodJ.gamma (Fin.last KJ.dividerCount))) ∧
          4 ≤ ((TreeMissingColors phi
                (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∩
              TreeMissingColors phi base.closure) \
            (HierarchyStoredColorsAt KJ
              (Fin.last KJ.dividerCount)).biUnion
                (goodJ.gamma (Fin.last KJ.dividerCount))).card) := by
-- BODY
  sorry
