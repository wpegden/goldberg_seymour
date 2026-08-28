import Tablet.BoundaryEdges
import Tablet.BoundaryColorEdges
import Tablet.DefectiveEdge
import Tablet.HkuIncidentColorPreserved
import Tablet.HkuMissingStoredMonotone
import Tablet.InternalEdges
import Tablet.MaximumDefectiveChoice
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeIncidentEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: SameColorSeriesPreserved]
theorem SameColorSeriesPreserved {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input) (p q : Fin rounds)
    (hpq : p.val ≤ q.val) (f : E) (c : Fin k)
    (hf : TreeIncidentEdge (series.data.tree p.succ.castSucc) f)
    (hfc : series.data.coloring p.castSucc f = some c)
    (hc : c ∈ TreeMissingColors (series.data.coloring p.castSucc)
          (series.data.tree p.succ.castSucc) ∪
        TashkinovStoredColors series.data p.castSucc) :
    (series.data.coloring q.succ f = series.data.coloring p.castSucc f ∨
      ∃ j : Fin rounds, p.val ≤ j.val ∧ j.val ≤ q.val ∧
        series.data.kind j.succ = some TashkinovExtensionKind.PE ∧
        series.data.connectingEdges j.succ = {f}) ∧
    (f ∈ InternalEdges G
          (TreeSequenceVertexSet (series.data.tree p.succ.castSucc)) →
      series.data.coloring q.succ f = series.data.coloring p.castSucc f) := by
-- BODY
  sorry
