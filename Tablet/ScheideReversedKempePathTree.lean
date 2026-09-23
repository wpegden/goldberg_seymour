import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.ScheideReversedPathCertificate
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ScheideReversedKempePathTree]
theorem ScheideReversedKempePathTree {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (htriple : KTriple G k e0 phi)
    (alpha beta : Fin k)
    (halpha : alpha ∈ MissingColors G phi
      (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩))
    (hbeta : beta ∈ MissingColors G phi
      (T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩))
    (p : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩))
      (Sum.inl (T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩)))
    (hp : p.IsPath) (hdiv : 4 ∣ p.length) :
    Nonempty (ScheideReversedPathCertificate G k e0 phi T alpha beta p) := by
-- BODY
  sorry
