import Tablet.TashkinovSeriesDataAppend
import Tablet.TashkinovStoredColors

-- [TABLET NODE: TashkinovStoredColorsAppend]
theorem TashkinovStoredColorsAppend {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    (data : TashkinovSeriesData G k rounds e0)
    (newTree : TreeSequence G e0)
    (newColoring : PartialEdgeColoring E k)
    (newStored : Finset (Fin k))
    (newConnectingEdges : Finset E)
    (newKind : Option TashkinovExtensionKind)
    (newChosenVertex newOutsideVertex : Option V)
    (newDelta newGamma : Option (Fin k))
    (i : Fin (rounds + 1)) :
    TashkinovStoredColors
      (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma)
      i.castSucc = TashkinovStoredColors data i := by
-- BODY
  classical
  unfold TashkinovStoredColors
  simp only [Fin.val_castSucc]
  split_ifs with hi
  · rfl
  · apply Finset.ext
    intro c
    rw [Finset.mem_sdiff, Finset.mem_sdiff]
    constructor
    · rintro ⟨hc, hmissing⟩
      rw [Finset.mem_biUnion] at hc
      rcases hc with ⟨h, -, hc⟩
      have hle : h.val ≤ i.val := by
        by_contra hn
        simp [hn] at hc
      simp [hle] at hc
      let oldH : Fin (rounds + 1) := ⟨h.val, lt_of_le_of_lt hle i.isLt⟩
      have hEq : h = oldH.castSucc := by ext; rfl
      have hcOld : c ∈ data.stored oldH := by
        rw [hEq] at hc
        simpa [TashkinovSeriesDataAppend] using hc
      have oldHle : oldH.val ≤ i.val := hle
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_biUnion]
        refine ⟨oldH, Finset.mem_univ _, ?_⟩
        simp only [if_pos oldHle]
        exact hcOld
      · simpa [TashkinovSeriesDataAppend] using hmissing
    · rintro ⟨hc, hmissing⟩
      rw [Finset.mem_biUnion] at hc
      rcases hc with ⟨h, -, hc⟩
      have hle : h.val ≤ i.val := by
        by_contra hn
        simp [hn] at hc
      simp [hle] at hc
      have hleCast : h.castSucc.val ≤ i.val := hle
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_biUnion]
        refine ⟨h.castSucc, Finset.mem_univ _, ?_⟩
        simp only [if_pos hleCast]
        simpa [TashkinovSeriesDataAppend] using hc
      · simpa [TashkinovSeriesDataAppend] using hmissing

