import Tablet.TashkinovSeriesDataPrefix
import Tablet.TashkinovStoredColors

-- [TABLET NODE: TashkinovStoredColorsPrefix]
theorem TashkinovStoredColorsPrefix {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    (m : ℕ) (hm : m ≤ rounds) (data : TashkinovSeriesData G k rounds e0)
    (i : Fin (m + 1)) :
    TashkinovStoredColors (TashkinovSeriesDataPrefix m hm data) i =
      TashkinovStoredColors data (Fin.castLE (by omega) i) := by
-- BODY
  classical
  unfold TashkinovStoredColors
  simp only [TashkinovSeriesDataPrefix]
  split <;> rename_i hz
  · rw [if_pos]
    exact hz
  · rw [if_neg]
    · congr 1
      ext c
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, hj⟩
        by_cases hji : j.val ≤ i.val
        · refine ⟨Fin.castLE (by omega) j, ?_⟩
          simpa [hji] using hj
        · simp [hji] at hj
      · rintro ⟨j, hj⟩
        by_cases hji : j.val ≤ i.val
        · let j' : Fin (m + 1) := ⟨j.val, by omega⟩
          refine ⟨j', ?_⟩
          simpa [j', hji] using hj
        · simp [hji] at hj
    · exact hz
