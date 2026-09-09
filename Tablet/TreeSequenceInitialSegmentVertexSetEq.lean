import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: TreeSequenceInitialSegmentVertexSetEq]
theorem TreeSequenceInitialSegmentVertexSetEq
    {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {e0 : E}
    (A B : TreeSequence G e0)
    (hAB : TreeSequenceInitialSegment A B)
    (hvertices : TreeSequenceVertexSet A = TreeSequenceVertexSet B) :
    A = B := by
-- BODY
  have hcard (S : TreeSequence G e0) :
      (TreeSequenceVertexSet S).card = S.length + 1 := by
    classical
    rw [TreeSequenceVertexSet, Finset.card_image_of_injective _ S.vertex_injective]
    simp
  have hlength : A.length = B.length := by
    have := congrArg Finset.card hvertices
    rw [hcard A, hcard B] at this
    omega
  rcases hAB with ⟨hlen, hvertex, hedge⟩
  cases A with
  | mk la pa va ea via eia fa aa =>
    cases B with
    | mk lb pb vb eb vib eib fb ab =>
      simp only at hlength
      subst lb
      rw [TreeSequence.mk.injEq]
      refine ⟨rfl, ?_, ?_⟩
      · apply heq_of_eq
        funext i
        simpa only [Fin.castLE] using (hvertex i).symm
      · apply heq_of_eq
        funext i
        simpa only [Fin.castLE] using (hedge i).symm
