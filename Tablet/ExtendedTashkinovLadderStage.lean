import Tablet.ExtendedTashkinovTree

-- [TABLET NODE: ExtendedTashkinovLadderStage]
def ExtendedTashkinovLadderStage {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (i : Fin (ett.rounds + 1)) : TreeSequence G e0 :=
-- BODY
  Fin.lastCases T
    (fun j : Fin ett.rounds => ett.series.data.tree j.succ.castSucc) i
