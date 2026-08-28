import Tablet.Degree
import Tablet.GlobalMaximumTriple
import Tablet.MissingColors

-- [TABLET NODE: ScheideGlobalMaximumMissingCounts]
theorem ScheideGlobalMaximumMissingCounts {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T)
    (v : V) (hv : v ∈ TreeSequenceVertexSet T) :
    (Incident G v e0 →
      (MissingColors G phi v).card = k - Degree G v + 1 ∧
        2 ≤ (MissingColors G phi v).card) ∧
    (¬ Incident G v e0 →
      (MissingColors G phi v).card = k - Degree G v ∧
        1 ≤ (MissingColors G phi v).card) := by
-- BODY
  sorry
