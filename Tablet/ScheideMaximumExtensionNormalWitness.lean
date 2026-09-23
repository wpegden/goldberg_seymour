import Tablet.FixedPairMaximalTashkinovTree
import Tablet.GlobalMaximumTriple
import Tablet.NormalGlobalMaximumTriple
import Tablet.ScheideMaximalExtendsEveryTree
import Tablet.ScheideReversedPathCertificate
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: ScheideMaximumExtensionNormalWitness]
theorem ScheideMaximumExtensionNormalWitness {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T)
    (hmax : FixedPairMaximalTashkinovTree G e0 phi T)
    (alpha beta : Fin k)
    (halpha : alpha ∈ MissingColors G phi
      (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩))
    (hbeta : beta ∈ MissingColors G phi
      (T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩))
    (p : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩))
      (Sum.inl (T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩)))
    (hp : p.IsPath)
    (C : ScheideReversedPathCertificate G k e0 phi T alpha beta p) :
    ∃ (T' : TreeSequence G e0)
      (N : NormalGlobalMaximumTriple G k e0 phi T'),
      N.height = p.length / 2 + 1 := by
-- BODY
  sorry
