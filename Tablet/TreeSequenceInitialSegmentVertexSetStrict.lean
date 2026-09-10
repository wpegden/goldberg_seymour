import Tablet.TreeSequenceInitialSegmentVertexSetSubset

-- [TABLET NODE: TreeSequenceInitialSegmentVertexSetStrict]
theorem TreeSequenceInitialSegmentVertexSetStrict
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : LooplessMultigraph V E} {e0 : E} {A B : TreeSequence G e0}
    (hAB : TreeSequenceInitialSegment A B) (hlen : A.length < B.length) :
    TreeSequenceVertexSet A < TreeSequenceVertexSet B := by
-- BODY
  have hsubset := TreeSequenceInitialSegmentVertexSetSubset hAB
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, ?_⟩
  intro heq
  have hcard : (TreeSequenceVertexSet A).card =
      (TreeSequenceVertexSet B).card := congrArg Finset.card heq
  have hcardA : (TreeSequenceVertexSet A).card = A.length + 1 := by
    simp [TreeSequenceVertexSet, Finset.card_image_of_injective,
      A.vertex_injective]
  have hcardB : (TreeSequenceVertexSet B).card = B.length + 1 := by
    simp [TreeSequenceVertexSet, Finset.card_image_of_injective,
      B.vertex_injective]
  rw [hcardA, hcardB] at hcard
  omega
