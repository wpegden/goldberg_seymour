import Tablet.ExtendedTashkinovTree

-- [TABLET NODE: ExtendedTashkinovColoringSequence]
def ExtendedTashkinovColoringSequence {V E : Type*} [Fintype V]
    [Fintype E] [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ}
    {e0 : E} {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating) :
    Fin (ett.rounds + 1) → PartialEdgeColoring E k :=
-- BODY
  ett.series.data.coloring
