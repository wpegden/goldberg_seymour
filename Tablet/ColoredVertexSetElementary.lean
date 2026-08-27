import Tablet.MissingColors

-- [TABLET NODE: ColoredVertexSetElementary]
def ColoredVertexSetElementary {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k)
    (X : Finset V) : Prop :=
-- BODY
  ∀ {u}, u ∈ X → ∀ {v}, v ∈ X → u ≠ v →
    Disjoint (MissingColors G phi u) (MissingColors G phi v)
