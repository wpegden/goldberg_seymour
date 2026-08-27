import Tablet.Incident

-- [TABLET NODE: InternalEdges]
noncomputable def InternalEdges {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) (U : Finset V) : Finset E := by
-- BODY
  classical
  exact Finset.univ.filter fun e => ∀ v, Incident G v e → v ∈ U
