import Tablet.IncidentCoreIncidence
import Tablet.IncidentVertexFintype
import Tablet.InternalEdges

-- [TABLET NODE: IncidentCoreInternalEdges]
theorem IncidentCoreInternalEdges {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) (U : Finset (IncidentVertex G)) :
    (U.map ⟨(fun x : IncidentVertex G => x.1), Subtype.coe_injective⟩).card =
        U.card ∧
      InternalEdges (IncidentCore G) U =
        InternalEdges G
          (U.map ⟨(fun x : IncidentVertex G => x.1), Subtype.coe_injective⟩) := by
-- BODY
  classical
  constructor
  · exact Finset.card_map _
  · unfold InternalEdges
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h v hv
      let x : IncidentVertex G := ⟨v, e, hv⟩
      have hx : x ∈ U := h x ((IncidentCoreIncidence G x e).2 hv)
      exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
    · intro h x hx
      have hv := h x.1 ((IncidentCoreIncidence G x e).1 hx)
      obtain ⟨y, hy, heq⟩ := Finset.mem_map.mp hv
      have hyx : y = x := Subtype.ext heq
      simpa [hyx] using hy
