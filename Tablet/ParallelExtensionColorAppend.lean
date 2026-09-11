import Tablet.ParallelExtensionColor
import Tablet.TashkinovSeriesDataAppend

-- [TABLET NODE: ParallelExtensionColorAppend]
theorem ParallelExtensionColorAppend {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    (data : TashkinovSeriesData G k rounds e0)
    (newTree : TreeSequence G e0)
    (newColoring : PartialEdgeColoring E k)
    (newStored : Finset (Fin k))
    (newConnectingEdges : Finset E)
    (newKind : Option TashkinovExtensionKind)
    (newChosenVertex newOutsideVertex : Option V)
    (newDelta newGamma : Option (Fin k))
    (i : Fin (rounds + 1)) (selected : PartialEdgeColoring E k)
    (v : V) (gamma : Fin k) :
    ParallelExtensionColor
      (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma)
      i.castSucc selected v gamma ↔
      ParallelExtensionColor data i selected v gamma := by
-- BODY
  let appended := TashkinovSeriesDataAppend data newTree newColoring
    newStored newConnectingEdges newKind newChosenVertex newOutsideVertex
    newDelta newGamma
  unfold ParallelExtensionColor
  constructor
  · rintro ⟨hmissing, history | noHistory⟩
    · rcases history with ⟨h, hpos, hle, hPE, hv, hdelta, hmax⟩
      let oldH : Fin (rounds + 1) := ⟨h.val, lt_of_le_of_lt hle i.isLt⟩
      have hEq : h = oldH.castSucc := by ext; rfl
      refine ⟨hmissing, Or.inl ⟨oldH, hpos, hle, ?_, ?_, ?_, ?_⟩⟩
      · simpa [appended, TashkinovSeriesDataAppend, hEq] using hPE
      · simpa [appended, TashkinovSeriesDataAppend, hEq] using hv
      · simpa [appended, TashkinovSeriesDataAppend, hEq] using hdelta
      · intro j hjpos hjle hjPE hjv
        exact hmax j.castSucc hjpos hjle
          (by simpa [appended, TashkinovSeriesDataAppend] using hjPE)
          (by simpa [appended, TashkinovSeriesDataAppend] using hjv)
    · refine ⟨hmissing, Or.inr ?_⟩
      intro h hpos hle hPE
      have newNe := noHistory h.castSucc hpos hle
        (by simpa [appended, TashkinovSeriesDataAppend] using hPE)
      simpa [appended, TashkinovSeriesDataAppend] using newNe
  · rintro ⟨hmissing, history | noHistory⟩
    · rcases history with ⟨h, hpos, hle, hPE, hv, hdelta, hmax⟩
      refine ⟨hmissing, Or.inl ⟨h.castSucc, hpos, hle, ?_, ?_, ?_, ?_⟩⟩
      · simpa [appended, TashkinovSeriesDataAppend] using hPE
      · simpa [appended, TashkinovSeriesDataAppend] using hv
      · simpa [appended, TashkinovSeriesDataAppend] using hdelta
      · intro j hjpos hjle hjPE hjv
        let oldJ : Fin (rounds + 1) := ⟨j.val, lt_of_le_of_lt hjle i.isLt⟩
        have jEq : j = oldJ.castSucc := by ext; rfl
        exact hmax oldJ hjpos hjle
          (by simpa [appended, TashkinovSeriesDataAppend, jEq] using hjPE)
          (by simpa [appended, TashkinovSeriesDataAppend, jEq] using hjv)
    · refine ⟨hmissing, Or.inr ?_⟩
      intro h hpos hle hPE
      let oldH : Fin (rounds + 1) := ⟨h.val, lt_of_le_of_lt hle i.isLt⟩
      have hEq : h = oldH.castSucc := by ext; rfl
      have oldNe := noHistory oldH hpos hle
        (by simpa [appended, TashkinovSeriesDataAppend, hEq] using hPE)
      simpa [appended, TashkinovSeriesDataAppend, hEq] using oldNe

