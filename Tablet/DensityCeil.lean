import Tablet.Density

-- [TABLET NODE: DensityCeil]
noncomputable def DensityCeil {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) : ℕ :=
-- BODY
  ⌈Density G⌉₊
