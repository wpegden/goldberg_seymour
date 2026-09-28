import Tablet.TchangeCounterexample

-- [TABLET NODE: TchangeCounterexampleMeasure]
def TchangeCounterexampleMeasure {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (C : TchangeCounterexample G k e0) : Nat :=
-- BODY
  C.P1.length + C.P2.length + C.P3.length
