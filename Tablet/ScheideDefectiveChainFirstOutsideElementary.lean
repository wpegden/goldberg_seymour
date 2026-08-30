import Tablet.AdjacentEdges
import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.GlobalMaximumTriple
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.ScheideDefectiveChainBoundaryEdges
import Tablet.ScheideDefectiveChainDepartureReturn
import Tablet.ScheideDefectiveChainPath
import Tablet.ScheideDepartureReturn
import Tablet.ScheideGlobalMaximumBoundaryFacts
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideGlobalMaximumUnused
import Tablet.TashkinovOrder
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TreeUsedColors
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ScheideDefectiveChainFirstOutsideElementary]
theorem ScheideDefectiveChainFirstOutsideElementary {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T)
    (alpha gamma : Fin k)
    (halpha : alpha ∈ DefectiveColors G phi (TreeSequenceVertexSet T))
    (hgammaFree : gamma ∈ TreeFreeColors phi T)
    (u : V) (hu : u ∈ TreeSequenceVertexSet T)
    (hgamma : gamma ∈ MissingColors G phi u)
    (z : V)
    (p : (TwoColorIncidenceGraph G phi alpha gamma).Walk
      (Sum.inl u) (Sum.inl z))
    (hp : ScheideDefectiveChainPath T phi alpha gamma u z p)
    (i1 i2 : Fin (p.length + 1)) (v1 v2 : V)
    (hdepart : ScheideDepartureReturn T i1 i2 v1 v2) :
    ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet T ∪ {v1}) := by
-- BODY
  sorry
