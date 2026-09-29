import Tablet.AdjacentEdges
import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetElementary
import Tablet.Incident
import Tablet.IsProperEdgeColoring
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.TreeColorSetClosed
import Tablet.TreeExitPath
import Tablet.TreeInterchangeable
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorNontrivialPathComponent
import Tablet.TwoColorPathComponent

-- [TABLET NODE: ElementaryClosedNoninterchangeableDisjointExitPaths]
lemma ElementaryClosedNoninterchangeableDisjointExitPaths {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
    (hproper : IsProperEdgeColoring G phi)
    (helementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet T))
    (a b : Fin k) (hne : a ≠ b)
    (hclosed : TreeColorSetClosed G phi T {a})
    (hnot : ¬ TreeInterchangeable G T phi a b) :
    ∃ (a1 b1 a2 b2 : V)
      (P1 : (TwoColorIncidenceGraph G phi a b).Walk
        (Sum.inl a1) (Sum.inl b1))
      (P2 : (TwoColorIncidenceGraph G phi a b).Walk
        (Sum.inl a2) (Sum.inl b2)),
      TreeExitPath T phi a b a1 b1 P1 ∧
      TreeExitPath T phi a b a2 b2 P2 ∧
      (∀ x, x ∈ P1.support → x ∉ P2.support) ∧
      a1 ≠ a2 ∧ b1 ≠ b2 := by
-- BODY
  sorry
