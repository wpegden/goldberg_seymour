import Tablet.AdjacentEdges
import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.DefectiveEdge
import Tablet.DefectiveVertex
import Tablet.Incident
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDefectiveChoice
import Tablet.MissingColors
import Tablet.ParallelExtensionColor
import Tablet.PresentColors
import Tablet.StableColoring
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeExit
import Tablet.TreeExitPath
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeVertexOrder
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.sc2

-- [TABLET NODE: HkuParallelBoundaryStructure]
theorem HkuParallelBoundaryStructure {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input) (q : Fin rounds)
    (f : E) (delta gamma : Fin k) (v : V)
    (hkind : series.data.kind q.succ = some TashkinovExtensionKind.PE)
    (hedge : series.data.connectingEdges q.succ = {f})
    (hdelta : series.data.delta q.succ = some delta)
    (hgamma : series.data.gamma q.succ = some gamma)
    (hvertex : series.data.chosenVertex q.succ = some v) :
    BoundaryColorEdges G (series.data.coloring q.succ)
        (TreeSequenceVertexSet (series.data.tree q.succ.castSucc)) gamma = {f} ∧
    (∀ g ∈ BoundaryColorEdges G (series.data.coloring q.succ)
        (TreeSequenceVertexSet (series.data.tree q.succ.castSucc)) delta,
      ∃ w : V, TreeVertexOrder (series.data.tree q.succ.castSucc) w v ∧
        Incident G w g) ∧
    (ColoredVertexSetElementary G (series.data.coloring q.castSucc)
        (TreeSequenceVertexSet (series.data.tree q.succ.castSucc)) →
      ∀ alpha ∈ TreeMissingColors (series.data.coloring q.succ)
          (series.data.tree q.succ.castSucc), alpha ≠ delta →
        BoundaryColorEdges G (series.data.coloring q.succ)
          (TreeSequenceVertexSet (series.data.tree q.succ.castSucc)) alpha = ∅) := by
-- BODY
  sorry
