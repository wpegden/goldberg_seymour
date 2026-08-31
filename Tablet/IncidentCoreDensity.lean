import Tablet.DensityCeil
import Tablet.DensityValue
import Tablet.EligibleOddSet
import Tablet.IncidentCoreInternalEdges

-- [TABLET NODE: IncidentCoreDensity]
theorem IncidentCoreDensity {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) :
    DensityCeil (IncidentCore G) ≤ DensityCeil G := by
-- BODY
  classical
  unfold DensityCeil Density
  dsimp
  apply Nat.ceil_mono
  apply Finset.max'_le
  intro q hq
  rcases Finset.mem_insert.mp hq with rfl | hq
  · exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  · rcases Finset.mem_image.mp hq with ⟨U, hU, rfl⟩
    let image : Finset V := U.map
      ⟨(fun x : IncidentVertex G => x.1), Subtype.coe_injective⟩
    have hdata := IncidentCoreInternalEdges G U
    have hcard : image.card = U.card := hdata.1
    have hodd : Odd image.card := by
      rw [hcard]
      exact (Finset.mem_filter.mp hU).2.2
    have hlarge : 3 ≤ image.card := by
      rw [hcard]
      exact (Finset.mem_filter.mp hU).2.1
    have himage : EligibleOddSet image := ⟨hlarge, hodd⟩
    have hvalue : DensityValue (IncidentCore G) U = DensityValue G image := by
      unfold DensityValue
      rw [hdata.2, hcard]
    rw [hvalue]
    exact Finset.le_max' _ _
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨image, by
        exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (by
          intro v hv
          exact Finset.mem_univ v), himage⟩, rfl⟩))
