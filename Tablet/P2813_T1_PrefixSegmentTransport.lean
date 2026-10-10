import Tablet.HierarchyFirstMissingPositionPrefixCutoff
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: P2813_T1_PrefixSegmentTransport]
theorem P2813_T1_PrefixSegmentTransport {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (phi sigma : PartialEdgeColoring E k) (U A T : TreeSequence G e0)
    (hUA : TreeSequenceInitialSegment U A)
    (hAT : TreeSequenceInitialSegment A T)
    (hfixed : ∀ t : Fin A.length, sigma (A.edge t) = phi (A.edge t))
    (hmissing : ∀ v ∈ TreeSequenceVertexSet A,
      MissingColors G sigma v = MissingColors G phi v)
    (eta : Fin k) (lower : Nat) :
    (Finset.univ.filter fun c : Fin k =>
      ∃ r : Fin U.length, lower ≤ r.val ∧
        r.val < min (HierarchyFirstMissingPosition sigma A eta).val U.length ∧
        sigma (U.edge r) = some c) =
    (Finset.univ.filter fun c : Fin k =>
      ∃ r : Fin U.length, lower ≤ r.val ∧
        r.val < min (HierarchyFirstMissingPosition phi T eta).val U.length ∧
        phi (U.edge r) = some c) := by
-- BODY
  classical
  have firstEq : HierarchyFirstMissingPosition sigma A eta =
      HierarchyFirstMissingPosition phi A eta := by
    have candidates :
        (Finset.univ.filter fun j : Fin (A.length + 1) =>
          eta ∈ MissingColors G sigma (A.vertex j)) =
        (Finset.univ.filter fun j : Fin (A.length + 1) =>
          eta ∈ MissingColors G phi (A.vertex j)) := by
      apply Finset.filter_congr
      intro j _
      have hj : A.vertex j ∈ TreeSequenceVertexSet A := by
        simp only [TreeSequenceVertexSet, Finset.mem_image,
          Finset.mem_univ, true_and]
        exact ⟨j, rfl⟩
      rw [hmissing _ hj]
    unfold HierarchyFirstMissingPosition
    rw [candidates]
  have cutoff := HierarchyFirstMissingPositionPrefixCutoff phi A T hAT eta U.length hUA.1
  rw [firstEq, cutoff]
  apply Finset.filter_congr
  intro c _
  constructor
  · rintro ⟨r, hr, hp, hc⟩
    refine ⟨r, hr, hp, ?_⟩
    have he : sigma (U.edge r) = phi (U.edge r) := by
      rw [← hUA.2.2 r]
      exact hfixed _
    exact he.symm.trans hc
  · rintro ⟨r, hr, hp, hc⟩
    refine ⟨r, hr, hp, ?_⟩
    have he : sigma (U.edge r) = phi (U.edge r) := by
      rw [← hUA.2.2 r]
      exact hfixed _
    exact he.trans hc
