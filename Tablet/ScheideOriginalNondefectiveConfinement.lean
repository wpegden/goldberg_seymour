import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.DefectiveColor
import Tablet.DefectiveColors
import Tablet.Incident
import Tablet.LooplessMultigraph
import Tablet.ScheideDefectiveSetup
import Tablet.ScheideEnlargedVertexSet
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideLastExitPath
import Tablet.ScheideReducedConfiguration
import Tablet.ScheideStructuralConfiguration
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ScheideOriginalNondefectiveConfinement]
theorem ScheideOriginalNondefectiveConfinement {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R : ∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d)
    (alpha : Fin k)
    (L : ScheideLastExitPath G k e0 phi T C D R alpha)
    (hlast : L.lastInside ∈ TreeSequenceVertexSet T)
    (hnondef : alpha ∉ DefectiveColors G phi (TreeSequenceVertexSet T)) :
    (∀ (j : Fin (L.path.length + 1)), j.val ≤ L.lastIndex.val →
      ∀ x : V, L.path.getVert j.val = Sum.inl x →
        x ∈ TreeSequenceVertexSet T) ∧
      ∀ f : E, f ∈ BoundaryEdges G (ScheideEnlargedVertexSet R) ∧
        Sum.inr f ∈ TwoColorComponent G phi D.alpha0 alpha
          (Sum.inl (C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩)) →
        f = L.crossing := by
-- BODY
  sorry
