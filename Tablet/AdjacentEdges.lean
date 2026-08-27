import Tablet.Incident

-- [TABLET NODE: AdjacentEdges]
def AdjacentEdges {V E : Type*} (G : LooplessMultigraph V E) (e f : E) : Prop :=
-- BODY
  ∃ v, Incident G v e ∧ Incident G v f
