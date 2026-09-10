import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: TreeSequenceInitialSegmentVertexSetSubset]
theorem TreeSequenceInitialSegmentVertexSetSubset
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : LooplessMultigraph V E} {e0 : E} {A B : TreeSequence G e0}
    (hAB : TreeSequenceInitialSegment A B) :
    TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
-- BODY
  intro v hv
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
    true_and] at hv ⊢
  obtain ⟨i, rfl⟩ := hv
  obtain ⟨hlen, hvertices, _⟩ := hAB
  exact ⟨Fin.castLE (Nat.succ_le_succ hlen) i, hvertices i⟩
