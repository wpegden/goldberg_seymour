import Tablet.ColoredVertexSetClosed
import Tablet.ETTFirstAppearanceIndex
import Tablet.ExtendedTashkinovTree
import Tablet.HkuMissingStoredMonotone
import Tablet.HkuParallelBoundaryStructure
import Tablet.HkuUnsupportedVertexColors
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumProperty
import Tablet.MissingColors
import Tablet.ParallelExtensionColor
import Tablet.RevisitingExtensionCertificate
import Tablet.SameColorSeriesPreserved
import Tablet.StableColoring
import Tablet.StableColoringBeforeVertex
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TechnicalTheoremBase
import Tablet.TechnicalTheoremBaseClaims
import Tablet.TechnicalTheoremClaims
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TreeExit
import Tablet.TreeExitPath
import Tablet.TreeVerticesBefore
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.sc2

-- [TABLET NODE: ExtensionRules]
theorem ExtensionRules {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E)
    (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett)
    (hbase : TechnicalTheoremBaseClaims ett.series)
    (hlower : ∀ {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input T' generating'),
      lower.rounds < ett.rounds → MaximumProperty lower →
      TechnicalTheoremClaims lower) :
    (∀ (q : Fin ett.rounds) (v : V),
      ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
      ett.series.data.chosenVertex q.succ = some v →
      ∀ hvFinal : v ∈ TreeSequenceVertexSet T,
      ∀ j : Fin (ett.rounds + 1),
        ETTFirstAppearanceIndex ett v hvFinal = j.val + 1 →
        ∀ sigma : PartialEdgeColoring E k,
          IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
          StableColoring (ett.series.data.tree q.succ.castSucc)
            (TashkinovStoredColors ett.series.data q.succ)
            (ett.series.data.coloring q.succ) sigma →
          StableColoringBeforeVertex T v
              (TashkinovStoredColors ett.series.data j)
              (ett.series.data.coloring j) sigma ∧
            StableColoring (ett.series.data.tree j.castSucc)
              (TashkinovStoredColors ett.series.data j)
              (ett.series.data.coloring j) sigma) ∧
    ∀ (q r : Fin ett.rounds) (vq vr : V),
      q ≠ r → vq ≠ vr →
      ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
      ett.series.data.kind r.succ = some TashkinovExtensionKind.PE →
      ett.series.data.chosenVertex q.succ = some vq →
      ett.series.data.chosenVertex r.succ = some vr →
      ∀ (hvq : vq ∈ TreeSequenceVertexSet T)
        (hvr : vr ∈ TreeSequenceVertexSet T),
        ETTFirstAppearanceIndex ett vq hvq =
          ETTFirstAppearanceIndex ett vr hvr →
        Disjoint (ett.series.data.stored q.succ)
          (ett.series.data.stored r.succ) := by
-- BODY
  sorry
