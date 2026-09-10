import Tablet.AlgorithmFiveFiveBaseStage
import Tablet.AlgorithmFiveSixFixedRootRefresh
import Tablet.ColoredVertexSetElementary
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ExtendedTashkinovTree
import Tablet.FiniteStrictGrowthReachesTerminal
import Tablet.GoodHierarchy
import Tablet.HierarchyBase
import Tablet.HierarchyBaseExists
import Tablet.HierarchyTerminalStoredColors
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDegree
import Tablet.MaximumProperty
import Tablet.ModColoring
import Tablet.ParallelSpecialClosurePreparation
import Tablet.StableColoring
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TashkinovClosureOfRouteAndAllMissingClosed
import Tablet.TashkinovClosureVertexSetUnique
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovHierarchy
import Tablet.TashkinovOrder
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TechnicalCurrentLadderMissingBoundLarge
import Tablet.TechnicalInductionContext
import Tablet.TreeColorSetClosed
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceAdjoinEdgeUnique
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceInitialSegmentVertexSetStrict
import Tablet.TreeSequenceVertexSet
import Tablet.sc2

-- [TABLET NODE: CurrentElementaryOrGoodHierarchyConstructionLarge]
theorem CurrentElementaryOrGoodHierarchyConstructionLarge
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett)
    (ctx : TechnicalInductionContext G k e0 ett.rounds)
    (hdegree : MaximumDegree G + 1 <= k)
    (hlarge : 11 <= TashkinovOrder G) :
    ColoredVertexSetElementary G generating (TreeSequenceVertexSet T) \/
      exists (U : TreeSequence G e0)
          (corrU : CorrespondingExtendedTashkinovTree
            G k e0 ett generating U),
        MaximumProperty corrU.replacementETT /\
          exists baseU : HierarchyBase corrU.replacementETT generating,
            exists H : TashkinovHierarchy corrU.replacementETT baseU,
              exists good : GoodHierarchy H,
                TreeColorSetClosed G generating U
                  (TreeMissingColors generating U) /\
                TreeSequenceVertexSet U =
                  TreeSequenceVertexSet
                    (ett.series.data.tree (Fin.last (ett.rounds + 1))) := by
-- BODY
  sorry
