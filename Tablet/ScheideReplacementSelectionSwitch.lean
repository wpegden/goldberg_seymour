import Tablet.AdjacentEdges
import Tablet.ColoredVertexSetClosed
import Tablet.DefectiveColor
import Tablet.DefectiveColors
import Tablet.GlobalMaximumTriple
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.ScheideEnlargedVertexSet
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideLastExitPath
import Tablet.ScheideReplacementData
import Tablet.ScheideSymmetricDefectiveInternal
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ScheideReplacementSelectionSwitch]
theorem ScheideReplacementSelectionSwitch {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R : ∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d)
    (alpha : Fin k)
    (L : ScheideLastExitPath G k e0 phi T C D R alpha)
    (hlast : L.lastInside ∉ TreeSequenceVertexSet T) :
    ∃ d : {delta // delta ∈ DefectiveColors G phi
        (TreeSequenceVertexSet T)},
      L.lastInside ∈ ({(R d).u1, (R d).u2} : Finset V) ∧
      TwoColorIncidenceGraph G
          (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
            (Sum.inl (D.v0 d))) D.alpha0 alpha =
        TwoColorIncidenceGraph G phi D.alpha0 alpha := by
-- BODY
  sorry
