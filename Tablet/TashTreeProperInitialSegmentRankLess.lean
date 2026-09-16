import Tablet.TashTreePathIndex
import Tablet.TashTreeRankLess
import Tablet.TashTreeSuffixPath
import Tablet.TreeSequenceInitialSegment

-- [TABLET NODE: TashTreeProperInitialSegmentRankLess]
theorem TashTreeProperInitialSegmentRankLess {V E : Type*}
    (G : LooplessMultigraph V E) {e0 : E} (S T : TreeSequence G e0)
    (hprefix : TreeSequenceInitialSegment S T)
    (hproper : S.length < T.length) : TashTreeRankLess G S T := by
-- BODY
  classical
  rcases hprefix with ⟨hlen, hvertex, hedge⟩
  have hspecS : TashTreeSuffixPath G S (TashTreePathIndex G S) := by
    unfold TashTreePathIndex
    exact Nat.find_spec _
  have hspecT : TashTreeSuffixPath G T (TashTreePathIndex G T) := by
    unfold TashTreePathIndex
    exact Nat.find_spec _
  let q := TashTreePathIndex G T
  have hpathSBound : TashTreePathIndex G S ≤ S.length := hspecS.2.1
  by_cases hshort : S.length < q
  · left
    exact hpathSBound.trans_lt hshort
  · have hqS : q ≤ S.length := Nat.le_of_not_gt hshort
    have hsuffixS : TashTreeSuffixPath G S q := by
      refine ⟨hspecT.1, hqS, ?_⟩
      intro i hi
      rw [← hedge i, ← hvertex i.castSucc, ← hvertex i.succ]
      exact hspecT.2.2 (Fin.castLE hlen i) hi
    have hindexLe : TashTreePathIndex G S ≤ q := by
      unfold TashTreePathIndex
      exact Nat.find_min' _ hsuffixS
    rcases hindexLe.eq_or_lt with heq | hlt
    · right
      exact ⟨heq, hproper⟩
    · left
      exact hlt
