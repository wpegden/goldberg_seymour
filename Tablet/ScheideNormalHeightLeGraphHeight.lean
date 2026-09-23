import Tablet.NormalGlobalMaximumTriple
import Tablet.ScheideGraphHeight
import Tablet.TreeSequence

-- [TABLET NODE: ScheideNormalHeightLeGraphHeight]
theorem ScheideNormalHeightLeGraphHeight {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T) :
    N.height ≤ ScheideGraphHeight G := by
-- BODY
  classical
  have hcard : T.length + 1 ≤ Fintype.card V := by
    simpa using Fintype.card_le_of_injective T.vertex T.vertex_injective
  have hNcard : N.height < Fintype.card V + 1 :=
    lt_of_le_of_lt N.height_upper (by omega)
  let heights := (Finset.range (Fintype.card V + 1)).filter fun p =>
    ∃ (m : ℕ) (f : E) (c : PartialEdgeColoring E m)
      (S : TreeSequence G f),
      ∃ M : NormalGlobalMaximumTriple G m f c S, M.height = p
  have hmem : N.height ∈ heights := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr hNcard, k, e0, phi, T, N, rfl⟩
  unfold ScheideGraphHeight
  dsimp only
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem hmem
