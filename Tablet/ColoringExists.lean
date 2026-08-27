import Tablet.HasKEdgeColoring

-- [TABLET NODE: ColoringExists]
theorem ColoringExists {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) : ∃ k, HasKEdgeColoring G k := by
-- BODY
  classical
  refine ⟨Fintype.card E, fun e => some (Fintype.equivFin E e), ?_, fun e => ?_⟩
  · intro e f c hne hadj he hf
    apply hne
    apply (Fintype.equivFin E).injective
    exact Option.some.inj (he.trans hf.symm)
  · exact ⟨Fintype.equivFin E e, rfl⟩
