import Tablet.AdjacentEdges
import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.DefectiveColors
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.ScheideDefectiveChainBoundaryEdges
import Tablet.ScheideDefectiveChainPath
import Tablet.ScheideDefectiveChainPathExists
import Tablet.ScheideDefectiveNoCross
import Tablet.ScheideDefectiveSetup
import Tablet.ScheideDefectiveSwitchEffect
import Tablet.ScheideExitNoFree
import Tablet.ScheideExitVertex
import Tablet.ScheideExitVertices
import Tablet.ScheideGlobalMaximumMissingCounts
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideReducedConfiguration
import Tablet.ScheideReplacementData
import Tablet.ScheideReplacementInternalMissing
import Tablet.ScheideReplacementMaximum
import Tablet.ScheideReplacementPairFixed
import Tablet.ScheideStructuralConfiguration
import Tablet.ScheideStructuralExitsInBase
import Tablet.ScheideStructuralInternalPair
import Tablet.TashkinovTree
import Tablet.TreeFreeColors
import Tablet.TreeSequence
import Tablet.TreeUsedColors
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph

open scoped Sym2

-- [TABLET NODE: ScheideSymmetricDefectiveInternal]
theorem ScheideSymmetricDefectiveInternal {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    (∃ f : E, phi f = some d.1 ∧
      G.ends f = s(C.blockVertex (D.gammaIndex d) 0,
        C.blockVertex (D.gammaIndex d) 1)) ∧
    ∃ f : E, phi f = some (C.gamma (D.gammaIndex d)) ∧
      G.ends f = s(R.u1, R.u2) := by
-- BODY
  sorry
