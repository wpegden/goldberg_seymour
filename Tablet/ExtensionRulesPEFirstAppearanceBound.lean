import Tablet.ETTFirstAppearanceIndex
import Tablet.ExtendedTashkinovLadderStage
import Tablet.MaximumDefectiveChoice
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: ExtensionRulesPEFirstAppearanceBound]
theorem ExtensionRulesPEFirstAppearanceBound {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (q : Fin ett.rounds) (v : V)
    (hkind : ett.series.data.kind q.succ = some TashkinovExtensionKind.PE)
    (hvertex : ett.series.data.chosenVertex q.succ = some v)
    (hvFinal : v ∈ TreeSequenceVertexSet T) :
    ETTFirstAppearanceIndex ett v hvFinal ≤ q.val + 1 := by
-- BODY
  sorry
