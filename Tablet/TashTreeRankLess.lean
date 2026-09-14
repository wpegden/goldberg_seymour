import Tablet.TashTreePathIndex

-- [TABLET NODE: TashTreeRankLess]
def TashTreeRankLess {V E : Type*} (G : LooplessMultigraph V E)
    {e0 : E} (S T : TreeSequence G e0) : Prop :=
-- BODY
  TashTreePathIndex G S < TashTreePathIndex G T ∨
    (TashTreePathIndex G S = TashTreePathIndex G T ∧ S.length < T.length)
