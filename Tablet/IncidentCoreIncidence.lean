import Tablet.IncidentCoreEndpoints
import Tablet.Incident

-- [TABLET NODE: IncidentCoreIncidence]
theorem IncidentCoreIncidence {V E : Type*} (G : LooplessMultigraph V E)
    (x : IncidentVertex G) (e : E) :
    Incident (IncidentCore G) x e ↔ Incident G x.1 e := by
-- BODY
  classical
  change x ∈ (IncidentCore G).ends e ↔ x.1 ∈ G.ends e
  constructor
  · intro hx
    rw [← IncidentCoreEndpoints G e]
    exact Sym2.mem_map.mpr ⟨x, hx, rfl⟩
  · intro hx
    have hx' : x.1 ∈ Sym2.map (fun y : IncidentVertex G => y.1)
        ((IncidentCore G).ends e) := by
      rw [IncidentCoreEndpoints G e]
      exact hx
    obtain ⟨y, hy, heq⟩ := Sym2.mem_map.mp hx'
    have : y = x := Subtype.ext heq
    simpa [this] using hy
