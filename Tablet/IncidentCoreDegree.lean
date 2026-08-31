import Tablet.Degree
import Tablet.IncidentCoreIncidence
import Tablet.IncidentVertexFintype

-- [TABLET NODE: IncidentCoreDegree]
theorem IncidentCoreDegree {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) (x : IncidentVertex G) :
    Degree (IncidentCore G) x = Degree G x.1 := by
-- BODY
  classical
  unfold Degree
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact IncidentCoreIncidence G x e
