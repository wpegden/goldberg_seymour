import Tablet.CertifiedETTRestriction
import Tablet.DefectiveVertex
import Tablet.IsOneEdgeUncolored
import Tablet.MaximumDefectiveChoice
import Tablet.MissingColors
import Tablet.ParallelExtensionColor
import Tablet.ParallelExtensionUndoStable
import Tablet.PresentColors
import Tablet.TechnicalInductionContext
import Tablet.TechnicalTheoremBase
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorPathComponent

-- [TABLET NODE: ParallelTerminalAwayInterchangeable]
theorem ParallelTerminalAwayInterchangeable {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (ctx : TechnicalInductionContext G k e0 ett.rounds)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (sigma : PartialEdgeColoring E k)
    (hproper : IsProperEdgeColoring G sigma)
    (hone : IsOneEdgeUncolored sigma e0)
    (hstable : StableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      phi sigma)
    (support : V) (gamma delta : Fin k)
    (hsupport : ett.series.data.chosenVertex (Fin.last ett.rounds) =
      some support)
    (hgamma : ett.series.data.gamma (Fin.last ett.rounds) = some gamma)
    (hdelta : ett.series.data.delta (Fin.last ett.rounds) = some delta) :
    let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
    ∀ alpha beta : Fin k,
      alpha ∈ TreeMissingColors sigma Tn →
      beta ∈ TreeMissingColors sigma Tn →
      alpha ≠ gamma → alpha ≠ delta →
      beta ≠ gamma → beta ≠ delta →
      TreeInterchangeable G Tn sigma alpha beta := by
-- BODY
  sorry
