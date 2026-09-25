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
import Tablet.ScheideDefectiveSetup
import Tablet.ScheideDefectiveSwitchEffect
import Tablet.ScheideEnlargedClosed
import Tablet.ScheideEnlargedElementary
import Tablet.ScheideEnlargedVertexSet
import Tablet.ScheideExitNoFree
import Tablet.ScheideExitVertex
import Tablet.ScheideExitVertices
import Tablet.ScheideGlobalMaximumMissingCounts
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideReducedConfiguration
import Tablet.ScheideReplacementData
import Tablet.ScheideReplacementMaximum
import Tablet.ScheideReplacementUnionClosed
import Tablet.ScheideStructuralConfiguration
import Tablet.ScheideStructuralExitsInBase
import Tablet.ScheideReplacementFamilyExists
import Tablet.ScheideOriginalDefectiveConfinement
import Tablet.ScheideOriginalNondefectiveConfinement
import Tablet.ScheideReplacementConfinement
import Tablet.ScheideSymmetricDefectiveInternal
import Tablet.ScheideTwoColorLastExitPath
import Tablet.TashkinovTree
import Tablet.TreeFreeColors
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TreeUsedColors
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph

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
  classical
  intro alpha hpresent
  let L : ScheideLastExitPath G k e0 phi T C D R alpha :=
    Classical.choice
      (ScheideTwoColorLastExitPath G k e0 phi T C D R alpha hpresent)
  refine ⟨L.crossing, ⟨L.crossingBoundary, L.crossingComponent⟩, ?_⟩
  intro f hf
  by_cases hlast : L.lastInside ∈ TreeSequenceVertexSet T
  · by_cases hdef : alpha ∈ DefectiveColors G phi (TreeSequenceVertexSet T)
    · exact (ScheideOriginalDefectiveConfinement G k e0 phi T C D R
        alpha L hlast hdef).2.2.2 f hf
    · exact (ScheideOriginalNondefectiveConfinement G k e0 phi T C D R
        alpha L hlast hdef).2 f hf
  · obtain ⟨d, _, _, _, _, _, _, hunique⟩ :=
      ScheideReplacementConfinement G k e0 phi T C D R alpha L hlast
    exact hunique f hf
