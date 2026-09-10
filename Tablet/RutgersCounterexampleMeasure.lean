import Tablet.RutgersCounterexample

-- [TABLET NODE: RutgersCounterexampleMeasure]
def RutgersCounterexampleMeasure
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    {original : ExtendedTashkinovTree G k e0 input T generating}
    {presentation : RutgersClosedPresentation G k e0 original}
    (counterexample : RutgersCounterexample G k e0 original presentation) : Nat :=
-- BODY
  counterexample.Q1.length + counterexample.Q2.length +
    counterexample.Q3.length
