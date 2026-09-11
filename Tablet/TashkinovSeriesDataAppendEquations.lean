import Tablet.TashkinovSeriesDataAppend

-- [TABLET NODE: TashkinovSeriesDataAppendEquations]
theorem TashkinovSeriesDataAppendEquations {V E : Type*}
    {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    (data : TashkinovSeriesData G k rounds e0)
    (newTree : TreeSequence G e0)
    (newColoring : PartialEdgeColoring E k)
    (newStored : Finset (Fin k))
    (newConnectingEdges : Finset E)
    (newKind : Option TashkinovExtensionKind)
    (newChosenVertex newOutsideVertex : Option V)
    (newDelta newGamma : Option (Fin k)) :
    let appended := TashkinovSeriesDataAppend data newTree newColoring
      newStored newConnectingEdges newKind newChosenVertex newOutsideVertex
      newDelta newGamma
    (∀ i : Fin (rounds + 2), appended.tree i.castSucc = data.tree i) ∧
    appended.tree (Fin.last (rounds + 2)) = newTree ∧
    (∀ i : Fin (rounds + 1),
      appended.coloring i.castSucc = data.coloring i ∧
      appended.stored i.castSucc = data.stored i ∧
      appended.connectingEdges i.castSucc = data.connectingEdges i ∧
      appended.kind i.castSucc = data.kind i ∧
      appended.chosenVertex i.castSucc = data.chosenVertex i ∧
      appended.outsideVertex i.castSucc = data.outsideVertex i ∧
      appended.delta i.castSucc = data.delta i ∧
      appended.gamma i.castSucc = data.gamma i) ∧
    appended.coloring (Fin.last (rounds + 1)) = newColoring ∧
    appended.stored (Fin.last (rounds + 1)) = newStored ∧
    appended.connectingEdges (Fin.last (rounds + 1)) = newConnectingEdges ∧
    appended.kind (Fin.last (rounds + 1)) = newKind ∧
    appended.chosenVertex (Fin.last (rounds + 1)) = newChosenVertex ∧
    appended.outsideVertex (Fin.last (rounds + 1)) = newOutsideVertex ∧
    appended.delta (Fin.last (rounds + 1)) = newDelta ∧
    appended.gamma (Fin.last (rounds + 1)) = newGamma := by
-- BODY
  simp [TashkinovSeriesDataAppend]

