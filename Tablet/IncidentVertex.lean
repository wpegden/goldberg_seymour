import Tablet.Incident

-- [TABLET NODE: IncidentVertex]
def IncidentVertex {V E : Type*} (G : LooplessMultigraph V E) :=
-- BODY
  {v : V // ∃ e : E, Incident G v e}
