import Tablet.ETTStrongInterchangeable
import Tablet.TreeInterchangeable
import Tablet.TwoColorPathComponent

-- [TABLET NODE: StrongInterchangeableImpliesInterchangeable]
theorem StrongInterchangeableImpliesInterchangeable {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating phi : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (t : Fin ett.rounds) (support : V) (alpha beta : Fin k)
    (hSI : ETTStrongInterchangeable ett t support phi alpha beta) :
    TreeInterchangeable G
      (ett.series.data.tree t.succ.castSucc) phi alpha beta := by
-- BODY
  sorry
