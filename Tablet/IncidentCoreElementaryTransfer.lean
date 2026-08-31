import Tablet.DensityLowerBound
import Tablet.Elementary
import Tablet.IncidentCoreChromaticIndex
import Tablet.IncidentCoreDensity

-- [TABLET NODE: IncidentCoreElementaryTransfer]
theorem IncidentCoreElementaryTransfer {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) (hcore : Elementary (IncidentCore G)) :
    Elementary G := by
-- BODY
  unfold Elementary at hcore ⊢
  apply Nat.le_antisymm
  · calc
      ChromaticIndex G = ChromaticIndex (IncidentCore G) :=
        (IncidentCoreChromaticIndex G).1.symm
      _ = DensityCeil (IncidentCore G) := hcore
      _ ≤ DensityCeil G := IncidentCoreDensity G
  · exact DensityLowerBound G
