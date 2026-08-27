import Tablet.MissingColors
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: TreeExitPath]
def TreeExitPath {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
    (alpha beta : Fin k) (u v : V)
    (p : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl u) (Sum.inl v)) :
    Prop :=
-- BODY
  p.IsPath ∧ 2 ≤ p.length ∧
    u ∉ TreeSequenceVertexSet T ∧ v ∈ TreeSequenceVertexSet T ∧
    (alpha ∈ MissingColors G phi u ∨ beta ∈ MissingColors G phi u) ∧
    ∀ w ∈ TreeSequenceVertexSet T, (Sum.inl w ∈ p.support ↔ w = v)
