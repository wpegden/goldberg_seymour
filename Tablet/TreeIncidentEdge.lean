import Tablet.Incident
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: TreeIncidentEdge]
def TreeIncidentEdge {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {e0 : E} (T : TreeSequence G e0) (f : E) : Prop :=
-- BODY
  ∃ v ∈ TreeSequenceVertexSet T, Incident G v f
