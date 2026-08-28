import Tablet.FixedPairMaximalTashkinovTree
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.NormalGlobalMaximumTriple
import Tablet.NormalTripleTrunk
import Tablet.ScheideGlobalMaximumMissingCounts
import Tablet.ScheideMaximalExtendsEveryTree
import Tablet.ScheideMaximalKempePath
import Tablet.TashkinovOrder
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ScheideNormalisation]
theorem ScheideNormalisation {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T) :
    ∃ (alpha beta : Fin k)
      (p : (TwoColorIncidenceGraph G phi alpha beta).Walk
        (Sum.inl (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩))
        (Sum.inl (T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩)))
      (T' : TreeSequence G e0)
      (N : NormalGlobalMaximumTriple G k e0 phi T'),
      alpha ∈ MissingColors G phi
          (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩) ∧
        beta ∈ MissingColors G phi
          (T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩) ∧
        p.IsPath ∧
        {x | x ∈ p.support} =
          TwoColorComponent G phi alpha beta
            (Sum.inl (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩)) ∧
        TreeSequenceVertexSet T' = TreeSequenceVertexSet T ∧
        N.alpha = alpha ∧ N.beta = beta ∧
        N.height = p.length / 2 + 1 := by
-- BODY
  sorry
