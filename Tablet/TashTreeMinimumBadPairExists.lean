import Tablet.TashTreeBadPair
import Tablet.TashTreeMinimumBadPair
import Tablet.TashTreePathIndex
import Tablet.TashTreeRankLess

-- [TABLET NODE: TashTreeMinimumBadPairExists]
theorem TashTreeMinimumBadPairExists {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (htriple : KTriple G k e0 phi) (hT : TashkinovTree G e0 phi T)
    (hbad : ¬ ColoredVertexSetElementary G phi (TreeSequenceVertexSet T)) :
    ∃ psi : PartialEdgeColoring E k, ∃ S : TreeSequence G e0,
      TashTreeMinimumBadPair G k e0 psi S := by
-- BODY
  classical
  let candidate : ℕ → ℕ → Prop := fun a b =>
    ∃ (psi : PartialEdgeColoring E k) (S : TreeSequence G e0),
      TashTreeBadPair G k e0 psi S ∧
        TashTreePathIndex G S = a ∧ S.length = b
  have candidateExists : ∃ a b, candidate a b := by
    exact ⟨TashTreePathIndex G T, T.length, phi, T,
      ⟨htriple, hT, hbad⟩, rfl, rfl⟩
  have firstExists : ∃ a, ∃ b, candidate a b := candidateExists
  let first : ℕ := Nat.find firstExists
  have firstSpec : ∃ b, candidate first b := Nat.find_spec firstExists
  let second : ℕ := Nat.find firstSpec
  have secondSpec : candidate first second := Nat.find_spec firstSpec
  obtain ⟨psi, S, hbadPair, hpath, hlength⟩ := secondSpec
  refine ⟨psi, S, hbadPair, ?_⟩
  intro psi' S' hbadPair'
  unfold TashTreeRankLess
  rw [hpath, hlength]
  intro hrank
  rcases hrank with hfirst | ⟨heq, hsecond⟩
  · have firstWitness : ∃ b, candidate (TashTreePathIndex G S') b := by
      exact ⟨S'.length, psi', S', hbadPair', rfl, rfl⟩
    have hminimal := Nat.find_min' firstExists firstWitness
    omega
  · have secondWitness : candidate first S'.length := by
      exact ⟨psi', S', hbadPair', heq, rfl⟩
    have hminimal := Nat.find_min' firstSpec secondWitness
    omega
