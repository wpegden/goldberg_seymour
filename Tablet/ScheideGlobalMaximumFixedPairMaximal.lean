import Tablet.FixedPairMaximalTashkinovTree
import Tablet.GlobalMaximumTriple
import Tablet.KTriple
import Tablet.TashkinovOrder
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: ScheideGlobalMaximumFixedPairMaximal]
theorem ScheideGlobalMaximumFixedPairMaximal {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T) :
    FixedPairMaximalTashkinovTree G e0 phi T := by
-- BODY
  classical
  refine ⟨hglobal.2.1, ?_⟩
  intro S hS hsub
  have hk : ChromaticIndex G - 1 = k := by
    have hchrom := hglobal.1.2.1
    omega
  have hScard : (TreeSequenceVertexSet S).card ≤ TashkinovOrder G := by
    unfold TashkinovOrder
    dsimp only
    apply Finset.le_max'
    apply Finset.mem_insert_of_mem
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ _))
    · rw [hk]
      exact ⟨e0, phi, S, hglobal.1, hS, rfl⟩
  have hcard : (TreeSequenceVertexSet S).card ≤
      (TreeSequenceVertexSet T).card := by
    rw [hglobal.2.2]
    exact hScard
  have heq : TreeSequenceVertexSet T = TreeSequenceVertexSet S :=
    Finset.eq_of_subset_of_card_le hsub hcard
  exact heq.symm.subset
