import ChallengeDeps

theorem ThmGS {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) :
    ChromaticIndex G ≤ max (MaximumDegree G + 1) (DensityCeil G) := by
  sorry
