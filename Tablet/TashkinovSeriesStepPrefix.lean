import Tablet.TashkinovSeriesDataPrefix
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColorsPrefix

-- [TABLET NODE: TashkinovSeriesStepPrefix]
theorem TashkinovSeriesStepPrefix {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    (input : PartialEdgeColoring E k)
    (data : TashkinovSeriesData G k rounds e0)
    (m : ℕ) (hm : m ≤ rounds) (i : Fin (m + 1))
    (cert : TashkinovSeriesStep G k rounds e0 input data
      (Fin.castLE (by omega) i)) :
    ∃ prefixCert : TashkinovSeriesStep G k m e0 input
        (TashkinovSeriesDataPrefix m hm data) i,
      HEq prefixCert cert := by
-- BODY
  sorry
