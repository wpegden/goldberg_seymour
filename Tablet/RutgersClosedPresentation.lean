import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.MaximumProperty
import Tablet.TashkinovClosure
import Tablet.TashkinovExtensionKind
import Tablet.TreeSequenceAdjoinEdge

-- [TABLET NODE: RutgersClosedPresentation]
structure RutgersClosedPresentation
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (original : ExtendedTashkinovTree G k e0 input T generating) where
-- BODY
  sigma : PartialEdgeColoring E k
  U : TreeSequence G e0
  corresponding :
    CorrespondingExtendedTashkinovTree G k e0 original sigma U
  maximum : MaximumProperty corresponding.replacementETT
  terminalRoute :
    let replacement := corresponding.replacementETT
    let n : Fin (replacement.rounds + 1) := Fin.last replacement.rounds
    let Tn : TreeSequence G e0 := replacement.series.data.tree n.castSucc
    (replacement.series.data.kind n = some TashkinovExtensionKind.PE /\
        TashkinovClosure sigma Tn U) \/
      ((replacement.series.data.kind n = some TashkinovExtensionKind.SE \/
          replacement.series.data.kind n = some TashkinovExtensionKind.RE) /\
        exists (f : E) (seed : TreeSequence G e0),
          replacement.series.data.connectingEdges n = {f} /\
            TreeSequenceAdjoinEdge Tn f seed /\
            TashkinovClosure sigma seed U)
