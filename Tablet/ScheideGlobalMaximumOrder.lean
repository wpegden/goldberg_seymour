import Tablet.GlobalMaximumTriple
import Tablet.ScheideMaximalElementaryClosed
import Tablet.ScheideMaximalOddOrder

-- [TABLET NODE: ScheideGlobalMaximumOrder]
theorem ScheideGlobalMaximumOrder {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T) :
    TashkinovOrder G = (TreeSequenceVertexSet T).card ∧
      3 ≤ (TreeSequenceVertexSet T).card ∧
      Odd (TreeSequenceVertexSet T).card ∧
      ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) ∧
      ColoredVertexSetClosed G phi (TreeSequenceVertexSet T) := by
-- BODY
  classical
  rcases hglobal with ⟨htriple, htree, hcard⟩
  have hmax : FixedPairMaximalTashkinovTree G e0 phi T := by
    refine ⟨htree, ?_⟩
    intro S hS hsubset
    have hle : (TreeSequenceVertexSet S).card ≤
        (TreeSequenceVertexSet T).card := by
      have hchi : ChromaticIndex G = k + 1 := htriple.2.1
      have hk : ChromaticIndex G - 1 = k := by
        omega
      have hmem : (TreeSequenceVertexSet S).card ∈
          (Finset.range (Fintype.card V + 1)).filter (fun n =>
            ∃ (e : E) (p : PartialEdgeColoring E (ChromaticIndex G - 1))
              (R : TreeSequence G e),
              KTriple G (ChromaticIndex G - 1) e p ∧
                TashkinovTree G e p R ∧
                  (TreeSequenceVertexSet R).card = n) := by
        rw [hk]
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · have hs : (TreeSequenceVertexSet S).card ≤ Fintype.card V :=
            Finset.card_le_card (Finset.subset_univ _)
          omega
        · refine ⟨e0, ?_, S, ?_, ?_, ?_⟩
          · exact phi
          · exact htriple
          · exact hS
          · rfl
      have horder : (TreeSequenceVertexSet S).card ≤ TashkinovOrder G := by
        unfold TashkinovOrder
        dsimp
        exact Finset.le_max' _ _ (Finset.mem_insert_of_mem hmem)
      exact horder.trans_eq hcard.symm
    have heq : TreeSequenceVertexSet S = TreeSequenceVertexSet T := by
      exact (Finset.eq_of_subset_of_card_le hsubset hle).symm
    rw [heq]
  have hodd := ScheideMaximalOddOrder G k e0 phi T htriple hmax
  have hec := ScheideMaximalElementaryClosed G k e0 phi T htriple hmax
  have htwo : 2 ≤ (TreeSequenceVertexSet T).card := by
    let v₀ : V := T.vertex ⟨0, Nat.zero_lt_succ _⟩
    have hp := T.positive
    let v₁ : V := T.vertex ⟨1, by omega⟩
    have hne : v₀ ≠ v₁ := by
      intro hv
      have hi := T.vertex_injective hv
      simp [v₀, v₁] at hi
    have hpair : ({v₀, v₁} : Finset V).card = 2 := by
      simp [hne]
    have hsub : ({v₀, v₁} : Finset V) ⊆ TreeSequenceVertexSet T := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · simp [TreeSequenceVertexSet, v₀]
      · simp [TreeSequenceVertexSet, v₁]
    rw [← hpair]
    exact Finset.card_le_card hsub
  have hthree : 3 ≤ (TreeSequenceVertexSet T).card := by
    rcases hodd with ⟨n, hn⟩
    omega
  exact ⟨hcard.symm, hthree, hodd, hec.1, hec.2⟩
