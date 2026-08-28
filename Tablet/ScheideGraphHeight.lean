import Tablet.NormalGlobalMaximumTriple

-- [TABLET NODE: ScheideGraphHeight]
noncomputable def ScheideGraphHeight {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) : ℕ := by
-- BODY
  classical
  let heights := (Finset.range (Fintype.card V + 1)).filter fun p =>
    ∃ (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0),
      ∃ N : NormalGlobalMaximumTriple G k e0 phi T, N.height = p
  exact (insert 0 heights).max' (by simp)
