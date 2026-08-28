import Tablet.TashkinovSeriesStep

-- [TABLET NODE: TashkinovSeries]
structure TashkinovSeries {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) where
-- BODY
  data : TashkinovSeriesData G k rounds e0
  certified : ∀ i : Fin (rounds + 1),
    TashkinovSeriesStep G k rounds e0 input data i
