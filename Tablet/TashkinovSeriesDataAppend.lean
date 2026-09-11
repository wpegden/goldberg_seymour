import Tablet.TashkinovSeriesData

-- [TABLET NODE: TashkinovSeriesDataAppend]
def TashkinovSeriesDataAppend {V E : Type*}
    {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    (data : TashkinovSeriesData G k rounds e0)
    (newTree : TreeSequence G e0)
    (newColoring : PartialEdgeColoring E k)
    (newStored : Finset (Fin k))
    (newConnectingEdges : Finset E)
    (newKind : Option TashkinovExtensionKind)
    (newChosenVertex newOutsideVertex : Option V)
    (newDelta newGamma : Option (Fin k)) :
    TashkinovSeriesData G k (rounds + 1) e0 :=
-- BODY
  {
    tree := Fin.lastCases newTree data.tree
    coloring := Fin.lastCases newColoring data.coloring
    stored := Fin.lastCases newStored data.stored
    connectingEdges := Fin.lastCases newConnectingEdges data.connectingEdges
    kind := Fin.lastCases newKind data.kind
    chosenVertex := Fin.lastCases newChosenVertex data.chosenVertex
    outsideVertex := Fin.lastCases newOutsideVertex data.outsideVertex
    delta := Fin.lastCases newDelta data.delta
    gamma := Fin.lastCases newGamma data.gamma
  }

