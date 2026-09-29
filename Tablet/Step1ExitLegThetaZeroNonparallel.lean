import Tablet.GoodHierarchy
import Tablet.HierarchyBase
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsCardinality
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyTerminalStoredColors
import Tablet.StableColoring
import Tablet.Step1ExitLegPresentation
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeColorSetMinusClosed
import Tablet.sc2

-- [TABLET NODE: Step1ExitLegThetaZeroNonparallel]
lemma Step1ExitLegThetaZeroNonparallel {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (n q : ℕ)
    (P : Step1ExitLegPresentation G k e0 n q)
    (hzero : P.hierarchy.dividerCount = 0)
    (hnonparallel : P.ett.series.data.kind (Fin.last P.ett.rounds) ≠
      some TashkinovExtensionKind.PE) :
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
