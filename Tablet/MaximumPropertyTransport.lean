import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.MaximumProperty
import Tablet.ModColoring
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.sc2

-- [TABLET NODE: MaximumPropertyTransport]
theorem MaximumPropertyTransport {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (base : ExtendedTashkinovTree G k e0 input T generating)
    (sigmaN : PartialEdgeColoring E k) (hmod : ModColoring base sigmaN)
    (Tstar : TreeSequence G e0)
    (corr : CorrespondingExtendedTashkinovTree G k e0 base sigmaN Tstar)
    (hMP : MaximumProperty base) : MaximumProperty corr.replacementETT := by
-- BODY
  sorry
