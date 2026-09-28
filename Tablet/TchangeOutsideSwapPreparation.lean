import Tablet.ColoredVertexSetClosed
import Tablet.KTriple
import Tablet.MissingColors
import Tablet.MissingColorsNonemptyOfMaximumDegree
import Tablet.OutsideTreeColorSwap
import Tablet.OutsideTreeColorSwapStable
import Tablet.TchangeCounterexampleMeasure
import Tablet.TashkinovTree
import Tablet.TreeExitPath
import Tablet.TreeVertexOrder

-- [TABLET NODE: TchangeOutsideSwapPreparation]
theorem TchangeOutsideSwapPreparation {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (C : TchangeCounterexample G k e0) :
    ∃ D : TchangeCounterexample G k e0,
      D.T = C.T ∧ D.b = C.b ∧
      D.phi = OutsideTreeColorSwap C.T C.phi C.a D.a ∧
      D.a ∈ MissingColors G D.phi D.b3 ∧
      TreeVertexOrder D.T D.b1 D.b3 ∧
      TreeVertexOrder D.T D.b2 D.b3 ∧
      TchangeCounterexampleMeasure D = TchangeCounterexampleMeasure C := by
-- BODY
  sorry
