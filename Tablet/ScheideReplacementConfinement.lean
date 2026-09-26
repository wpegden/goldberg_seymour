import Tablet.AdjacentEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetElementary
import Tablet.ColoredVertexSetClosed
import Tablet.DefectiveColor
import Tablet.DefectiveColors
import Tablet.GlobalMaximumTriple
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.MissingColors
import Tablet.ScheideDefectiveSetup
import Tablet.ScheideDefectiveSwitchEffect
import Tablet.ScheideEnlargedVertexSet
import Tablet.ScheideExitNoFree
import Tablet.ScheideExitVertex
import Tablet.ScheideExitVertices
import Tablet.ScheideGlobalMaximumMissingCounts
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideLastExitPath
import Tablet.ScheideReplacementData
import Tablet.ScheideReplacementBoundaryUnique
import Tablet.ScheideReplacementExitNotDefective
import Tablet.ScheideReplacementMaximum
import Tablet.ScheideReplacementPathPrefix
import Tablet.ScheideReplacementSelectionSwitch
import Tablet.ScheideReplacementUsedWitness
import Tablet.ScheideReducedConfiguration
import Tablet.ScheideStructuralConfiguration
import Tablet.ScheideStructuralExitsInBase
import Tablet.ScheideSymmetricDefectiveInternal
import Tablet.TashkinovTree
import Tablet.TreeFreeColors
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TreeUsedColors
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ScheideReplacementConfinement]
theorem ScheideReplacementConfinement {V E : Type*}
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
        TwoColorIncidenceGraph G phi D.alpha0 alpha ∧
      (∀ c ∈ TreeUsedColors
          (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
            (Sum.inl (D.v0 d))) (R d).replacementTree,
        ∃ z ∈ TreeSequenceVertexSet T \
            {C.blockVertex (D.gammaIndex d) 0,
              C.blockVertex (D.gammaIndex d) 1},
          c ∈ MissingColors G
            (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
              (Sum.inl (D.v0 d))) z) ∧
      (∃ beta,
        beta ∈ MissingColors G
          (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
            (Sum.inl (D.v0 d))) L.lastInside ∧
        beta ∈ TreeFreeColors
          (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
            (Sum.inl (D.v0 d))) (R d).replacementTree) ∧
      alpha ∉ DefectiveColors G
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
          (Sum.inl (D.v0 d)))
        (TreeSequenceVertexSet (R d).replacementTree) ∧
      (∀ (j : Fin (L.path.length + 1)), j.val ≤ L.lastIndex.val →
        ∀ x : V, L.path.getVert j.val = Sum.inl x →
          x ∈ TreeSequenceVertexSet (R d).replacementTree) ∧
      ∀ f : E, f ∈ BoundaryEdges G (ScheideEnlargedVertexSet R) ∧
        Sum.inr f ∈ TwoColorComponent G phi D.alpha0 alpha
          (Sum.inl (C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩)) →
        f = L.crossing := by
-- BODY
  obtain ⟨d, hpair, hgraph⟩ :=
    ScheideReplacementSelectionSwitch G k e0 phi T C D R alpha L hlast
  have hused := ScheideReplacementUsedWitness G k e0 phi T C D R d
  obtain ⟨hfree, hnondef⟩ :=
    ScheideReplacementExitNotDefective G k e0 phi T C D R alpha L hlast
      d hpair hgraph
  have hprefix := ScheideReplacementPathPrefix G k e0 phi T C D R alpha L
    d hpair hgraph hnondef
  have hboundary := ScheideReplacementBoundaryUnique G k e0 phi T C D R
    alpha L d hprefix
  exact ⟨d, hpair, hgraph, hused, hfree, hnondef, hprefix, hboundary⟩
