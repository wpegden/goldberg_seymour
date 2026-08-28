import Tablet.ScheideExitVertex
import Tablet.TreeExit

-- [TABLET NODE: ScheideExitVertexTreeExit]
theorem ScheideExitVertexTreeExit {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (v : V)
    (hexit : ScheideExitVertex T phi v) :
    ∃ gamma delta : Fin k,
      delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T) ∧
        TreeExit T phi delta gamma v := by
-- BODY
  sorry
