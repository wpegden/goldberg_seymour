import Tablet.ExtendedTashkinovTree

-- [TABLET NODE: ExtendedTashkinovRungNumber]
def ExtendedTashkinovRungNumber {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating) : ℕ :=
-- BODY
  ett.rounds
