import Tablet.DensityLowerBound
import Tablet.DensityMonotone
import Tablet.Elementary

-- [TABLET NODE: ElementaryTransfer]
theorem ElementaryTransfer {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) (F : Finset E)
    (hχ : ChromaticIndex (RestrictEdges G F) = ChromaticIndex G)
    (hElem : Elementary (RestrictEdges G F)) : Elementary G := by
-- BODY
  sorry
