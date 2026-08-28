import Tablet.ScheideDefectiveChainBoundaryEdges
import Tablet.ScheideEnlargedClosed
import Tablet.ScheideReplacementUnionClosed
import Tablet.ScheideStructuralExitsInBase
import Tablet.ScheideReplacementFamilyExists
import Tablet.ScheideSymmetricDefectiveInternal
import Tablet.TwoColorComponentSpanningPath

-- [TABLET NODE: ScheideSingleBoundaryCrossing]
theorem ScheideSingleBoundaryCrossing {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R : ∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d) :
    ∀ alpha : Fin k,
      (∀ v ∈ ScheideEnlargedVertexSet R, alpha ∈ PresentColors G phi v) →
      ∃! f : E, f ∈ BoundaryEdges G (ScheideEnlargedVertexSet R) ∧
        Sum.inr f ∈ TwoColorComponent G phi D.alpha0 alpha
          (Sum.inl (C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩)) := by
-- BODY
  sorry
