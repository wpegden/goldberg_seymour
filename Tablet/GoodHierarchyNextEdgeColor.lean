import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchySegmentColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeColorSetClosed
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: GoodHierarchyNextEdgeColor]
theorem GoodHierarchyNextEdgeColor {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T phi}
    {base : HierarchyBase ett phi} {H : TashkinovHierarchy ett base}
    (good : GoodHierarchy H) (i : Fin H.dividerCount) :
    let current := H.stage i.succ.castSucc
    let next := H.stage i.succ.succ
    ∃ r : Fin next.length, ∃ alpha eta : Fin k,
      r.val = current.length ∧
      phi (next.edge r) = some alpha ∧
      eta ∈ HierarchyStoredColorsAt H i.succ ∧
      alpha ∈ good.gamma i.castSucc eta ∧
      alpha ∉ good.gamma i.succ eta := by
-- BODY
  sorry
