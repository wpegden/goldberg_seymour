import Tablet.ChromaticIndex

-- [TABLET NODE: ChromaticIndexSpec]
theorem ChromaticIndexSpec {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) :
    HasKEdgeColoring G (ChromaticIndex G) ∧
      ∀ k, HasKEdgeColoring G k → ChromaticIndex G ≤ k := by
-- BODY
  classical
  constructor
  · exact Nat.find_spec (ColoringExists G)
  · intro k hk
    exact Nat.find_min' (ColoringExists G) hk
