import Tablet.IncidentCoreIncidence

-- [TABLET NODE: IncidentCoreNoIsolated]
theorem IncidentCoreNoIsolated {V E : Type*} (G : LooplessMultigraph V E) :
    ∀ x : IncidentVertex G, ∃ e : E, Incident (IncidentCore G) x e := by
-- BODY
  intro x
  obtain ⟨e, he⟩ := x.2
  exact ⟨e, (IncidentCoreIncidence G x e).2 he⟩
