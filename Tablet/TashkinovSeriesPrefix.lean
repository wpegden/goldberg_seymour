import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStepPrefix

-- [TABLET NODE: TashkinovSeriesPrefix]
theorem TashkinovSeriesPrefix {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input)
    (m : ℕ) (hm : m ≤ rounds) :
    ∃ restricted : TashkinovSeries G k m e0 input,
      restricted.data = TashkinovSeriesDataPrefix m hm series.data ∧
      ∀ i : Fin (m + 1), HEq (restricted.certified i)
        (series.certified (Fin.castLE (by omega) i)) := by
-- BODY
  let restricted : TashkinovSeries G k m e0 input := {
    data := TashkinovSeriesDataPrefix m hm series.data
    certified := fun i =>
      (TashkinovSeriesStepPrefix input series.data m hm i
        (series.certified (Fin.castLE (by omega) i))).choose
  }
  refine ⟨restricted, rfl, ?_⟩
  intro i
  exact (TashkinovSeriesStepPrefix input series.data m hm i
    (series.certified (Fin.castLE (by omega) i))).choose_spec
