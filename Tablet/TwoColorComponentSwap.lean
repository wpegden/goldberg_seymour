import Tablet.TwoColorComponent

-- [TABLET NODE: TwoColorComponentSwap]
noncomputable def TwoColorComponentSwap {V E : Type*}
    (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k)
    (alpha beta : Fin k) (z : Sum V E) : PartialEdgeColoring E k := by
-- BODY
  classical
  exact fun e =>
    if Sum.inr e ∈ TwoColorComponent G phi alpha beta z then
      if phi e = some alpha then some beta
      else if phi e = some beta then some alpha
      else phi e
    else phi e
