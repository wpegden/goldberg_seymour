import Tablet.DensityLowerBound
import Tablet.DensityMonotone
import Tablet.Elementary

-- [TABLET NODE: ElementaryTransfer]
theorem ElementaryTransfer {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) (F : Finset E)
    (hχ : ChromaticIndex (RestrictEdges G F) = ChromaticIndex G)
    (hElem : Elementary (RestrictEdges G F)) : Elementary G := by
-- BODY
  unfold Elementary at hElem ⊢
  have lowerBound : DensityCeil G ≤ ChromaticIndex G := DensityLowerBound G
  have upperBound : ChromaticIndex G ≤ DensityCeil G := by
    calc
      ChromaticIndex G = ChromaticIndex (RestrictEdges G F) := hχ.symm
      _ = DensityCeil (RestrictEdges G F) := hElem
      _ ≤ DensityCeil G := DensityMonotone G F
  exact le_antisymm upperBound lowerBound
