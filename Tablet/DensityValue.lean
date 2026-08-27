import Tablet.InternalEdges

-- [TABLET NODE: DensityValue]
noncomputable def DensityValue {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) (U : Finset V) : ℚ :=
-- BODY
  (2 * (InternalEdges G U).card : ℚ) / (U.card - 1)
