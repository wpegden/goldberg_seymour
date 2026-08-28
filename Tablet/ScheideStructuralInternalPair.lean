import Tablet.AdjacentEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.DefectiveColors
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.ScheideDefectiveChainPath
import Tablet.ScheideExitNoFree
import Tablet.ScheideExitVertex
import Tablet.ScheideExitVertices
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideGlobalMaximumBoundaryFacts
import Tablet.ScheideReducedConfiguration
import Tablet.ScheideStructuralConfiguration
import Tablet.TashkinovTree
import Tablet.TreeFreeColors
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TreeUsedColors

open scoped Sym2

-- [TABLET NODE: ScheideStructuralInternalPair]
theorem ScheideStructuralInternalPair {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T) :
    ∀ (i : Fin C.s) (alpha : Fin k), alpha ≠ C.gamma i →
      (∃ z ∈ TreeSequenceVertexSet T \
          {C.blockVertex i 0, C.blockVertex i 1},
        alpha ∈ MissingColors G phi z) →
      ∃ f : E, phi f = some alpha ∧
        G.ends f = s(C.blockVertex i 0, C.blockVertex i 1) := by
-- BODY
  sorry
