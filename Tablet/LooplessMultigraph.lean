import Tablet.Preamble

open scoped Sym2

-- [TABLET NODE: LooplessMultigraph]
structure LooplessMultigraph (V E : Type*) where
-- BODY
  ends : E → Sym2 V
  loopless : ∀ e v, ends e ≠ s(v, v)
