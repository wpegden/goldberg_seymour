import Tablet.HierarchyFirstMissingPosition
import Tablet.MissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment

-- [TABLET NODE: HierarchyFirstMissingPositionPrefixCutoff]
lemma HierarchyFirstMissingPositionPrefixCutoff {V E : Type*}
    [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (phi : PartialEdgeColoring E k) (A T : TreeSequence G e0)
    (hAT : TreeSequenceInitialSegment A T) (eta : Fin k)
    (uLength : Nat) (hu : uLength <= A.length) :
    min (HierarchyFirstMissingPosition phi A eta).val uLength =
      min (HierarchyFirstMissingPosition phi T eta).val uLength := by
-- BODY
  classical
  let candidatesA : Finset (Fin (A.length + 1)) :=
    {i | eta ∈ MissingColors G phi (A.vertex i)}
  let candidatesT : Finset (Fin (T.length + 1)) :=
    {i | eta ∈ MissingColors G phi (T.vertex i)}
  unfold HierarchyFirstMissingPosition
  dsimp only
  change min (if h : candidatesA.Nonempty then candidatesA.min' h
      else Fin.last A.length).val uLength =
    min (if h : candidatesT.Nonempty then candidatesT.min' h
      else Fin.last T.length).val uLength
  by_cases hA : candidatesA.Nonempty
  · rw [dif_pos hA]
    let mA := candidatesA.min' hA
    let mAT : Fin (T.length + 1) :=
      Fin.castLE (Nat.succ_le_succ hAT.1) mA
    have hmAmem : mA ∈ candidatesA := Finset.min'_mem candidatesA hA
    have hmATmem : mAT ∈ candidatesT := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hmA : eta ∈ MissingColors G phi (A.vertex mA) :=
        (Finset.mem_filter.mp hmAmem).2
      rw [hAT.2.1 mA]
      exact hmA
    have hT : candidatesT.Nonempty := ⟨mAT, hmATmem⟩
    rw [dif_pos hT]
    have hTle : (candidatesT.min' hT).val <= mA.val := by
      have hFin := Finset.min'_le candidatesT mAT hmATmem
      change (candidatesT.min' hT).val <= mAT.val at hFin
      simpa [mAT] using hFin
    let mTA : Fin (A.length + 1) :=
      ⟨(candidatesT.min' hT).val, by omega⟩
    have hmTmem : candidatesT.min' hT ∈ candidatesT :=
      Finset.min'_mem candidatesT hT
    have hmTAmem : mTA ∈ candidatesA := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hmT : eta ∈ MissingColors G phi
          (T.vertex (candidatesT.min' hT)) :=
        (Finset.mem_filter.mp hmTmem).2
      have hcast : Fin.castLE (Nat.succ_le_succ hAT.1) mTA =
          candidatesT.min' hT := Fin.ext rfl
      rw [← hcast, hAT.2.1 mTA] at hmT
      exact hmT
    have hAle : mA.val <= (candidatesT.min' hT).val := by
      have hFin := Finset.min'_le candidatesA mTA hmTAmem
      change (candidatesA.min' hA).val <= mTA.val at hFin
      simpa [mTA, mA] using hFin
    have heq : mA.val = (candidatesT.min' hT).val := by omega
    rw [heq]
  · rw [dif_neg hA]
    by_cases hT : candidatesT.Nonempty
    · rw [dif_pos hT]
      have hbound : A.length <= (candidatesT.min' hT).val := by
        by_contra hnot
        have hlt : (candidatesT.min' hT).val < A.length := by omega
        let mTA : Fin (A.length + 1) :=
          ⟨(candidatesT.min' hT).val, by omega⟩
        have hmTmem : candidatesT.min' hT ∈ candidatesT :=
          Finset.min'_mem candidatesT hT
        have hmTAmem : mTA ∈ candidatesA := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          have hmT : eta ∈ MissingColors G phi
              (T.vertex (candidatesT.min' hT)) :=
            (Finset.mem_filter.mp hmTmem).2
          have hcast : Fin.castLE (Nat.succ_le_succ hAT.1) mTA =
              candidatesT.min' hT := Fin.ext rfl
          rw [← hcast, hAT.2.1 mTA] at hmT
          exact hmT
        exact hA ⟨mTA, hmTAmem⟩
      simp only [Fin.val_last]
      omega
    · rw [dif_neg hT]
      simp only [Fin.val_last]
      have hlen := hAT.1
      omega
