import Tablet.ETTStrongInterchangeable
import Tablet.ExtendedTashkinovTree
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.LooplessMultigraph
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentCycle
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorCycle
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorNontrivialPathComponent

-- [TABLET NODE: StrongInterchangeabilityKempePreserved]
theorem StrongInterchangeabilityKempePreserved {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (s t : Fin ett.rounds) (vs vt : V)
    (gammaS deltaS gammaT deltaT : Fin k)
    (phi : PartialEdgeColoring E k) (z : Sum V E)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (hgammaS : ett.series.data.gamma s.succ = some gammaS)
    (hdeltaS : ett.series.data.delta s.succ = some deltaS)
    (hgammaT : ett.series.data.gamma t.succ = some gammaT)
    (hdeltaT : ett.series.data.delta t.succ = some deltaT)
    (hrelative : vs ≠ vt ∨ s.val < t.val)
    (hdifferentColors : vs ≠ vt →
      Disjoint ({gammaS, deltaS} : Finset (Fin k)) {gammaT, deltaT})
    (hpath : TwoColorNontrivialPathComponent G phi gammaT deltaT z)
    (htSI : ETTStrongInterchangeable ett t vt phi gammaT deltaT)
    (hsSI : ETTStrongInterchangeable ett s vs phi gammaS deltaS) :
    let phiStar := TwoColorComponentSwap G phi gammaT deltaT z
    IsProperEdgeColoring G phiStar ∧ IsOneEdgeUncolored phiStar e0 ∧
      ETTStrongInterchangeable ett s vs phiStar gammaS deltaS := by
-- BODY
  sorry
