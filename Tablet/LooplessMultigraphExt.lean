import Tablet.LooplessMultigraph

-- [TABLET NODE: LooplessMultigraphExt]
theorem LooplessMultigraphExt {V E : Type*} (G H : LooplessMultigraph V E)
    (h : G.ends = H.ends) : G = H := by
-- BODY
  cases G
  cases H
  simp_all
