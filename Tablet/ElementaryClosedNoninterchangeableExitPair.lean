import Tablet.AdjacentEdges
import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetElementary
import Tablet.ClosedColorExitPathBoundaryEdge
import Tablet.ElementaryClosedNoninterchangeableDisjointExitPaths
import Tablet.Incident
import Tablet.IsProperEdgeColoring
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.TreeColorSetClosed
import Tablet.TreeExitPath
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorNontrivialPathComponent
import Tablet.TwoColorPathComponent

-- [TABLET NODE: ElementaryClosedNoninterchangeableExitPair]
lemma ElementaryClosedNoninterchangeableExitPair {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
    (hproper : IsProperEdgeColoring G phi)
    (helementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet T))
    (a b : Fin k) (hne : a ≠ b)
    (hamissing : a ∈ TreeMissingColors phi T)
    (hclosed : TreeColorSetClosed G phi T {a})
    (hnot : ¬ TreeInterchangeable G T phi a b) :
    ∃ (a1 b1 a2 b2 : V)
      (P1 : (TwoColorIncidenceGraph G phi a b).Walk
        (Sum.inl a1) (Sum.inl b1))
      (P2 : (TwoColorIncidenceGraph G phi a b).Walk
        (Sum.inl a2) (Sum.inl b2))
      (f1 f2 : E),
      TreeExitPath T phi a b a1 b1 P1 ∧
      TreeExitPath T phi a b a2 b2 P2 ∧
      (∀ x, x ∈ P1.support → x ∉ P2.support) ∧
      a1 ≠ a2 ∧ b1 ≠ b2 ∧
      f1 ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) b ∧
      f2 ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) b ∧
      Incident G b1 f1 ∧ Incident G b2 f2 ∧
      Sum.inr f1 ∈ P1.support ∧ Sum.inr f2 ∈ P2.support := by
-- BODY
  obtain ⟨a1, b1, a2, b2, P1, P2, hP1, hP2, hdisjoint, ha, hb⟩ :=
    ElementaryClosedNoninterchangeableDisjointExitPaths G T phi hproper
      helementary a b hne hclosed hnot
  obtain ⟨f1, hf1, hi1, hs1⟩ :=
    ClosedColorExitPathBoundaryEdge G T phi a b hclosed a1 b1 P1 hP1
  obtain ⟨f2, hf2, hi2, hs2⟩ :=
    ClosedColorExitPathBoundaryEdge G T phi a b hclosed a2 b2 P2 hP2
  exact ⟨a1, b1, a2, b2, P1, P2, f1, f2, hP1, hP2, hdisjoint,
    ha, hb, hf1, hf2, hi1, hi2, hs1, hs2⟩
