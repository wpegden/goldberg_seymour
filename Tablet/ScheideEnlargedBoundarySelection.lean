import Tablet.AdjacentEdges
import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetStronglyClosed
import Tablet.DefectiveColors
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.InternalEdges
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.ScheideDefectiveSetup
import Tablet.ScheideEnlargedClosed
import Tablet.ScheideEnlargedVertexSet
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideReducedConfiguration
import Tablet.ScheideReplacementData
import Tablet.ScheideReplacementPairsLaminar
import Tablet.ScheideReplacementUnionClosed
import Tablet.ScheideSingleBoundaryCrossing
import Tablet.ScheideStructuralConfiguration
import Tablet.ScheideSymmetricDefectiveInternal
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorIncidenceGraph

open scoped Sym2

-- [TABLET NODE: ScheideEnlargedBoundarySelection]
theorem ScheideEnlargedBoundarySelection {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R : ∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d)
    (hnot : ¬ ColoredVertexSetStronglyClosed G phi
      (ScheideEnlargedVertexSet R)) :
    ∃ (alpha : Fin k)
      (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
      (f : E) (w u : V),
      alpha ≠ D.alpha0 ∧
      phi f = some alpha ∧
      G.ends f = s(w, u) ∧
      w ∈ ScheideEnlargedVertexSet R ∧
      w ∉ TreeSequenceVertexSet T ∧
      u ∉ ScheideEnlargedVertexSet R ∧
      (w = (R d).u1 ∨ w = (R d).u2) ∧
      Sum.inr f ∈ TwoColorComponent G phi D.alpha0 alpha (Sum.inl u) ∧
      ∀ v ∈ TreeSequenceVertexSet T,
        Sum.inl v ∉ TwoColorComponent G phi D.alpha0 alpha (Sum.inl u) := by
-- BODY
  sorry
