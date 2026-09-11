import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStepAppend

-- [TABLET NODE: TashkinovSeriesAppend]
theorem TashkinovSeriesAppend {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input)
    (newTree : TreeSequence G e0)
    (newColoring : PartialEdgeColoring E k)
    (newStored : Finset (Fin k))
    (newConnectingEdges : Finset E)
    (newKind : Option TashkinovExtensionKind)
    (newChosenVertex newOutsideVertex : Option V)
    (newDelta newGamma : Option (Fin k))
    (lastCertified : TashkinovSeriesStep G k (rounds + 1) e0 input
      (TashkinovSeriesDataAppend series.data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma)
      (Fin.last (rounds + 1))) :
    ∃ extended : TashkinovSeries G k (rounds + 1) e0 input,
      extended.data = TashkinovSeriesDataAppend series.data newTree
        newColoring newStored newConnectingEdges newKind newChosenVertex
        newOutsideVertex newDelta newGamma := by
-- BODY
  let appended := TashkinovSeriesDataAppend series.data newTree newColoring
    newStored newConnectingEdges newKind newChosenVertex newOutsideVertex
    newDelta newGamma
  let extended : TashkinovSeries G k (rounds + 1) e0 input := {
    data := appended
    certified := by
      intro i
      refine Fin.lastCases lastCertified ?_ i
      intro oldIndex
      exact TashkinovSeriesStepAppend G k rounds e0 input series.data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma
        oldIndex (series.certified oldIndex)
  }
  exact ⟨extended, rfl⟩
