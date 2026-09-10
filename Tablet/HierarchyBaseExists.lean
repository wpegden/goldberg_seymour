import Tablet.AdjacentEdges
import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.DefectiveColor
import Tablet.DefectiveEdge
import Tablet.DefectiveVertex
import Tablet.ExtendedTashkinovTree
import Tablet.HierarchyBase
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDefectiveChoice
import Tablet.OrderedTreeUnionExists
import Tablet.TashkinovClosureExists
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeSequencePrefix
import Tablet.TreeVertexOrder

-- [TABLET NODE: HierarchyBaseExists]
theorem HierarchyBaseExists
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating) :
    Nonempty (HierarchyBase ett generating) := by
-- BODY
  sorry
