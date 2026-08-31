import Tablet.IncidentVertex

noncomputable section

-- [TABLET NODE: IncidentVertexFintype]
instance IncidentVertexFintype {V E : Type*} [Fintype V]
    (G : LooplessMultigraph V E) : Fintype (IncidentVertex G) := by
-- BODY
  classical
  unfold IncidentVertex
  infer_instance
