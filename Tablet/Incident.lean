import Tablet.LooplessMultigraph

-- [TABLET NODE: Incident]
def Incident {V E : Type*} (G : LooplessMultigraph V E) (v : V) (e : E) : Prop :=
-- BODY
  v ∈ G.ends e
