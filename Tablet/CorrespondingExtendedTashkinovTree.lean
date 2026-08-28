import Tablet.ExtendedTashkinovColoringSequence
import Tablet.ExtendedTashkinovLadderStage
import Tablet.ExtendedTashkinovRungNumber
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.StableColoring
import Tablet.TashkinovStoredColors

-- [TABLET NODE: CorrespondingExtendedTashkinovTree]
structure CorrespondingExtendedTashkinovTree {V E : Type*} [Fintype V]
    [Fintype E] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (base : ExtendedTashkinovTree G k e0 input T generating)
    (sigmaN : PartialEdgeColoring E k) (Tstar : TreeSequence G e0) where
-- BODY
  replacementInput : PartialEdgeColoring E k
  replacementSeries : TashkinovSeries G k base.rounds e0 replacementInput
  replacementETT :
    ExtendedTashkinovTree G k e0 replacementInput Tstar sigmaN
  rungAgreement : replacementETT.rounds = base.rounds
  seriesPresentation : HEq replacementETT.series replacementSeries
  finalGeneratingColoring :
    sigmaN = replacementSeries.data.coloring (Fin.last base.rounds)
  ladderTreesAgree : ∀ i : Fin base.rounds,
    replacementSeries.data.tree i.succ.castSucc =
      base.series.data.tree i.succ.castSucc
  storedColorsAgree : ∀ i : Fin (base.rounds + 1),
    replacementSeries.data.stored i = base.series.data.stored i
  connectingEdgesAgree : ∀ i : Fin (base.rounds + 1),
    replacementSeries.data.connectingEdges i =
      base.series.data.connectingEdges i
  extensionKindsAgree : ∀ i : Fin (base.rounds + 1),
    replacementSeries.data.kind i = base.series.data.kind i
  replacementProper : ∀ i : Fin (base.rounds + 1),
    IsProperEdgeColoring G (replacementSeries.data.coloring i)
  replacementOneUncolored : ∀ i : Fin (base.rounds + 1),
    IsOneEdgeUncolored (replacementSeries.data.coloring i) e0
  replacementStable : ∀ i : Fin base.rounds,
    StableColoring (base.series.data.tree i.succ.castSucc)
      (TashkinovStoredColors base.series.data i.succ)
      (base.series.data.coloring i.succ)
      (replacementSeries.data.coloring i.succ)
