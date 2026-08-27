import Tablet.ChromaticIndexSpec
import Tablet.MaximumDegree

-- [TABLET NODE: MaximumDegreeLowerBound]
theorem MaximumDegreeLowerBound {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) : MaximumDegree G ≤ ChromaticIndex G := by
-- BODY
  classical
  obtain ⟨φ, hproper, hfull⟩ := (ChromaticIndexSpec G).1
  unfold MaximumDegree
  apply Finset.max'_le
  simp only [Finset.mem_insert, Finset.mem_image]
  intro y hy
  rcases hy with rfl | ⟨v, hv, degree_value⟩
  · exact Nat.zero_le _
  · rw [← degree_value]
    change (Finset.univ.filter (fun e => Incident G v e)).card ≤ ChromaticIndex G
    let color : E → Fin (ChromaticIndex G) := fun e => Classical.choose (hfull e)
    have color_spec : ∀ e, φ e = some (color e) := by
      intro e
      exact Classical.choose_spec (hfull e)
    have injective_on : Set.InjOn color
        (↑(Finset.univ.filter (fun e => Incident G v e)) : Set E) := by
      intro e he f hf equal_colors
      by_contra unequal_edges
      have edge_mem_e : e ∈ Finset.univ.filter (fun e => Incident G v e) := he
      have edge_mem_f : f ∈ Finset.univ.filter (fun e => Incident G v e) := hf
      apply hproper unequal_edges
        ⟨v, (Finset.mem_filter.mp edge_mem_e).2,
          (Finset.mem_filter.mp edge_mem_f).2⟩ (color_spec e)
      rw [color_spec f, equal_colors]
    have bounded := Finset.card_le_card_of_injOn color
        (s := Finset.univ.filter (fun e => Incident G v e))
        (t := (Finset.univ : Finset (Fin (ChromaticIndex G)))) (by simp) injective_on
    simpa using bounded
