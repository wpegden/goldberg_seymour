import Tablet.Incident

-- [TABLET NODE: Degree]
noncomputable def Degree {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) (v : V) : ℕ := by
-- BODY
  classical
  exact (Finset.univ.filter fun e => Incident G v e).card
