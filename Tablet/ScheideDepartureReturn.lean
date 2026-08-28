import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
import Tablet.ScheideDefectiveChainPath

-- [TABLET NODE: ScheideDepartureReturn]
def ScheideDepartureReturn {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) {phi : PartialEdgeColoring E k}
    {alpha gamma : Fin k} {u z : V}
    {p : (TwoColorIncidenceGraph G phi alpha gamma).Walk
      (Sum.inl u) (Sum.inl z)}
    (i1 i2 : Fin (p.length + 1)) (v1 v2 : V) : Prop :=
-- BODY
  ScheideDefectiveChainPath T phi alpha gamma u z p ∧
    p.getVert i1.val = Sum.inl v1 ∧
    v1 ∉ TreeSequenceVertexSet T ∧
    (∀ r : Fin (p.length + 1), r.val < i1.val →
      ∀ w : V, p.getVert r.val = Sum.inl w →
        w ∈ TreeSequenceVertexSet T) ∧
    i1.val < i2.val ∧
    p.getVert i2.val = Sum.inl v2 ∧
    v2 ∈ TreeSequenceVertexSet T ∧
    ∀ r : Fin (p.length + 1), i2.val < r.val →
      ∀ w : V, p.getVert r.val = Sum.inl w →
        w ∉ TreeSequenceVertexSet T
