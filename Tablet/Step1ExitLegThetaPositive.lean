import Tablet.GoodHierarchy
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsCardinality
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyTerminalStoredColors
import Tablet.OrderedTreeUnion
import Tablet.Step1ExitLegMinimum
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeMissingColors

-- [TABLET NODE: Step1ExitLegThetaPositive]
lemma Step1ExitLegThetaPositive {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (n q : ℕ)
    (M : Step1ExitLegMinimum G k e0 n q)
    (hpositive : 0 < M.selected.hierarchy.dividerCount) :
    ∃ theta : Fin k,
      theta ≠ M.selected.a ∧ theta ≠ M.selected.b ∧
      theta ∈ TreeMissingColors M.selected.phi
        (HierarchyStarredStage M.selected.hierarchy
          (Fin.last M.selected.hierarchy.dividerCount)) ∧
      TreeColorSetClosed G M.selected.phi
        (HierarchyStarredStage M.selected.hierarchy
          (Fin.last M.selected.hierarchy.dividerCount)) {theta} ∧
      TreeColorSetClosed G M.selected.phi M.selected.T {theta} := by
-- BODY
  sorry
