import Tablet.ExtendedTashkinovTree
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.StableColoring
import Tablet.TashkinovClosure
import Tablet.TashkinovStoredColors
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: TerminalClosureMaximum]
def TerminalClosureMaximum
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating) : Prop :=
-- BODY
  let idx : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Ti : TreeSequence G e0 := ett.series.data.tree idx.castSucc
  forall (pi : PartialEdgeColoring E k) (seed candidate : TreeSequence G e0),
    IsProperEdgeColoring G pi -> IsOneEdgeUncolored pi e0 ->
    StableColoring Ti (TashkinovStoredColors ett.series.data idx)
      (ett.series.data.coloring idx) pi ->
    ((ett.series.data.kind idx = some TashkinovExtensionKind.PE /\ seed = Ti) \/
      ((ett.series.data.kind idx = some TashkinovExtensionKind.SE \/
          ett.series.data.kind idx = some TashkinovExtensionKind.RE) /\
        exists f : E, ett.series.data.connectingEdges idx = {f} /\
          TreeSequenceAdjoinEdge Ti f seed)) ->
    TashkinovClosure pi seed candidate ->
    (TreeSequenceVertexSet candidate).card <=
      (TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last (ett.rounds + 1)))).card
