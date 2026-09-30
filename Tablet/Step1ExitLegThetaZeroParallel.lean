import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyBase
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsCardinality
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyTerminalStoredColors
import Tablet.OrderedTreeUnion
import Tablet.ParallelCommonMissingClosed
import Tablet.Step1ExitLegPresentation
import Tablet.TashkinovHierarchy
import Tablet.TreeColorSetClosed
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeMissingColors

-- [TABLET NODE: Step1ExitLegThetaZeroParallel]
lemma Step1ExitLegThetaZeroParallel {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (n q : ℕ)
    (P : Step1ExitLegPresentation G k e0 n q)
    (hzero : P.hierarchy.dividerCount = 0)
    (hparallel : P.ett.series.data.kind (Fin.last P.ett.rounds) =
      some TashkinovExtensionKind.PE)
    (hpre :
      let r : Fin P.ett.rounds := ⟨P.ett.rounds - 1, by
        have h := P.ett.roundsPositive
        omega⟩
      ColoredVertexSetElementary G
        (P.ett.series.data.coloring r.castSucc)
        (TreeSequenceVertexSet
          (P.ett.series.data.tree (Fin.last P.ett.rounds).castSucc))) :
    ∃ theta : Fin k,
      theta ≠ P.a ∧ theta ≠ P.b ∧
      theta ∈ TreeMissingColors P.phi
        (HierarchyStarredStage P.hierarchy
          (Fin.last P.hierarchy.dividerCount)) ∧
      TreeColorSetClosed G P.phi
        (HierarchyStarredStage P.hierarchy
          (Fin.last P.hierarchy.dividerCount)) {theta} ∧
      TreeColorSetClosed G P.phi P.T {theta} := by
-- BODY
  sorry
