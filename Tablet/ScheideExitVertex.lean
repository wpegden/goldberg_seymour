import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
import Tablet.DefectiveColors
import Tablet.MissingColors
import Tablet.ScheideDefectiveChainPath

-- [TABLET NODE: ScheideExitVertex]
def ScheideExitVertex {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (v : V) : Prop :=
-- BODY
  ∃ (u : V) (gamma delta : Fin k),
    u ∈ TreeSequenceVertexSet T ∧
      gamma ∈ MissingColors G phi u ∧
      delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T) ∧
      ∃ (z : V)
        (p : (TwoColorIncidenceGraph G phi delta gamma).Walk
          (Sum.inl u) (Sum.inl z)),
        ScheideDefectiveChainPath T phi delta gamma u z p ∧
          ∃ i : Fin (p.length + 1),
            p.getVert i.val = Sum.inl v ∧
              v ∈ TreeSequenceVertexSet T ∧
              ∀ r : Fin (p.length + 1), i.val < r.val →
                ∀ w : V, p.getVert r.val = Sum.inl w →
                  w ∉ TreeSequenceVertexSet T
