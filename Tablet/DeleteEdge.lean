import Tablet.RestrictEdges

-- [TABLET NODE: DeleteEdge]
noncomputable def DeleteEdge {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (e0 : E) :
    LooplessMultigraph V {e // e ∈ Finset.univ.erase e0} :=
-- BODY
  RestrictEdges G (Finset.univ.erase e0)
