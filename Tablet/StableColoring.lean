import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors

-- [TABLET NODE: StableColoring]
def StableColoring {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (C : Finset (Fin k))
    (phi pi : PartialEdgeColoring E k) : Prop :=
-- BODY
  (∀ f, TreeIncidentEdge T f →
      (∃ c ∈ TreeMissingColors phi T ∪ C, phi f = some c) → pi f = phi f) ∧
    ∀ v ∈ TreeSequenceVertexSet T, MissingColors G pi v = MissingColors G phi v
