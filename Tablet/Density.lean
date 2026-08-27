import Tablet.DensityValue
import Tablet.EligibleOddSet

-- [TABLET NODE: Density]
noncomputable def Density {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) : ℚ := by
-- BODY
  classical
  let eligible := Finset.univ.powerset.filter fun U : Finset V => EligibleOddSet U
  let values := eligible.image (DensityValue G)
  exact (insert 0 values).max' (by simp)
