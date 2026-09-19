import Tablet.ColoredVertexSetElementary
import Tablet.TashTreeBadPair
import Tablet.TashTreeMinimumBadPair
import Tablet.TashTreePathIndex
import Tablet.TashTreeRankLess
import Tablet.TashTreeSuffixPath
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: TashTreePathIndexTwoReplacement]
theorem TashTreePathIndexTwoReplacement {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hlen : 2 ≤ T.length) (hq : TashTreePathIndex G T = 2) :
    ∃ S : TreeSequence G e0,
      (∃ hST : S.length = T.length,
        (∀ r : Fin S.length,
          S.edge r = T.edge (Fin.cast hST r)) ∧
        S.vertex ⟨0, Nat.zero_lt_succ S.length⟩ =
          T.vertex ⟨1, by omega⟩ ∧
        S.vertex ⟨1, by omega⟩ =
          T.vertex ⟨0, Nat.zero_lt_succ T.length⟩ ∧
        (∀ r : Fin (S.length + 1), 2 ≤ r.val →
          S.vertex r = T.vertex
            (Fin.cast (congrArg (fun n => n + 1) hST) r))) ∧
      TashTreeBadPair G k e0 phi S ∧
      TashTreeRankLess G S T := by
-- BODY
  classical
  let z : Fin (T.length + 1) := ⟨0, by omega⟩
  let o : Fin (T.length + 1) := ⟨1, by omega⟩
  have hswapZ : Equiv.swap z o z = o := Equiv.swap_apply_left z o
  have hswapO : Equiv.swap z o o = z := Equiv.swap_apply_right z o
  have hswapLater (r : Fin (T.length + 1)) (hr : 2 ≤ r.val) :
      Equiv.swap z o r = r := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h
      have hz : r.val = 0 := by simpa [z] using congrArg Fin.val h
      omega
    · intro h
      have ho : r.val = 1 := by simpa [o] using congrArg Fin.val h
      omega
  have hspecT : TashTreeSuffixPath G T (TashTreePathIndex G T) := by
    unfold TashTreePathIndex
    exact Nat.find_spec _
  have hsuffix2 : TashTreeSuffixPath G T 2 := by
    simpa [hq] using hspecT
  have hedgeOne :
      G.ends (T.edge ⟨1, by omega⟩) =
        s(T.vertex ⟨2, by omega⟩, T.vertex z) := by
    rcases T.attaches ⟨1, by omega⟩ with ⟨i, hi⟩
    by_cases hi0 : i.val = 0
    · rw [hi]
      apply (Sym2.eq_iff).2
      left
      constructor
      · congr 1
      · congr 1
        apply Fin.ext
        simpa [z] using hi0
    · have hilimit : i.val < 2 := by simpa using i.isLt
      have hi1 : i.val = 1 := by omega
      have hbadEdge :
          G.ends (T.edge ⟨1, by omega⟩) =
            s(T.vertex ⟨1, by omega⟩, T.vertex ⟨2, by omega⟩) := by
        rw [hi]
        apply (Sym2.eq_iff).2
        right
        constructor <;> congr 1 <;> apply Fin.ext <;> simp [hi1]
      have hsuffix1 : TashTreeSuffixPath G T 1 := by
        refine ⟨by omega, by omega, ?_⟩
        intro j hj
        by_cases hj1 : j.val = 1
        · have hjeq : j = ⟨1, by omega⟩ := Fin.ext hj1
          rw [hjeq]
          exact hbadEdge
        · exact hsuffix2.2.2 j (by omega)
      have hle : TashTreePathIndex G T ≤ 1 := by
        unfold TashTreePathIndex
        exact Nat.find_min' _ hsuffix1
      omega
  let S : TreeSequence G e0 :=
    { length := T.length
      positive := T.positive
      vertex := fun r => T.vertex (Equiv.swap z o r)
      edge := T.edge
      vertex_injective := by
        intro a b hab
        exact (Equiv.swap z o).injective (T.vertex_injective hab)
      edge_injective := T.edge_injective
      first_edge := T.first_edge
      attaches := by
        intro j
        by_cases hj0 : j.val = 0
        · have hj : j = ⟨0, T.positive⟩ := Fin.ext hj0
          rw [hj]
          rcases T.attaches ⟨0, T.positive⟩ with ⟨i, hi⟩
          have hi0 : i = 0 := Fin.eq_zero i
          subst i
          refine ⟨0, ?_⟩
          rw [hi]
          apply (Sym2.eq_iff).2
          right
          constructor
          · change T.vertex ⟨1, by omega⟩ = T.vertex (Equiv.swap z o z)
            rw [hswapZ]
          · change T.vertex z = T.vertex (Equiv.swap z o o)
            rw [hswapO]
        · by_cases hj1 : j.val = 1
          · have hj : j = ⟨1, by omega⟩ := Fin.ext hj1
            rw [hj]
            refine ⟨⟨1, by omega⟩, ?_⟩
            rw [hedgeOne]
            apply (Sym2.eq_iff).2
            left
            constructor
            · congr 1
            · change T.vertex z = T.vertex (Equiv.swap z o o)
              rw [hswapO]
          · refine ⟨⟨j.val, by omega⟩, ?_⟩
            rw [hsuffix2.2.2 j (by omega)]
            apply (Sym2.eq_iff).2
            right
            constructor
            · congr 1
              rw [hswapLater]
              apply Fin.ext
              rfl
              change 2 ≤ j.val
              omega
            · congr 1
              rw [hswapLater]
              change 2 ≤ j.val + 1
              omega }
  have hlength : S.length = T.length := rfl
  have hedge (r : Fin S.length) : S.edge r = T.edge (Fin.cast hlength r) := rfl
  have hvertexZero :
      S.vertex ⟨0, Nat.zero_lt_succ S.length⟩ = T.vertex ⟨1, by omega⟩ := by
    change T.vertex (Equiv.swap z o z) = T.vertex o
    rw [hswapZ]
  have hvertexOne :
      S.vertex ⟨1, by omega⟩ = T.vertex ⟨0, Nat.zero_lt_succ T.length⟩ := by
    change T.vertex (Equiv.swap z o o) = T.vertex z
    rw [hswapO]
  have hvertexLater (r : Fin (S.length + 1)) (hr : 2 ≤ r.val) :
      S.vertex r = T.vertex
        (Fin.cast (congrArg (fun n => n + 1) hlength) r) := by
    change T.vertex (Equiv.swap z o r) = T.vertex r
    rw [hswapLater r hr]
  have hTash : TashkinovTree G e0 phi S := by
    intro j hj
    rcases hmin.1.2.1 j hj with ⟨i, c, hcolor, hmissing⟩
    let old : Fin (T.length + 1) :=
      Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt))
    let new : Fin (T.length + 1) := Equiv.swap z o old
    have hnewBound : new.val < j.val + 1 := by
      simp only [new, Equiv.swap_apply_def]
      split_ifs with hz ho
      · simp [o]
        omega
      · simp [z]
      · simpa [old] using i.isLt
    let i' : Fin (j.val + 1) := ⟨new.val, hnewBound⟩
    refine ⟨i', c, ?_, ?_⟩
    · exact hcolor
    · have hv : S.vertex
          (Fin.castLT i' (Nat.lt_trans i'.isLt (Nat.succ_lt_succ j.isLt))) =
          T.vertex (Fin.castLT i
            (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt))) := by
        have hcast :
            Fin.castLT i' (Nat.lt_trans i'.isLt (Nat.succ_lt_succ j.isLt)) = new := by
          apply Fin.ext
          rfl
        change T.vertex (Equiv.swap z o
            (Fin.castLT i' (Nat.lt_trans i'.isLt
              (Nat.succ_lt_succ j.isLt)))) = T.vertex old
        rw [hcast]
        apply congrArg T.vertex
        exact Equiv.swap_apply_self z o old
      rw [hv]
      exact hmissing
  have hvertexSet : TreeSequenceVertexSet S = TreeSequenceVertexSet T := by
    apply Finset.ext
    intro v
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨Equiv.swap z o r, rfl⟩
    · rintro ⟨r, rfl⟩
      refine ⟨Equiv.swap z o r, ?_⟩
      change T.vertex (Equiv.swap z o (Equiv.swap z o r)) = T.vertex r
      rw [Equiv.swap_apply_self]
  have hbadS : TashTreeBadPair G k e0 phi S := by
    refine ⟨hmin.1.1, hTash, ?_⟩
    simpa [hvertexSet] using hmin.1.2.2
  have hsuffixS : TashTreeSuffixPath G S 1 := by
    refine ⟨by omega, by simpa [S] using T.positive, ?_⟩
    intro j hj
    by_cases hj1 : j.val = 1
    · change G.ends (T.edge j) =
        s(T.vertex (Equiv.swap z o j.castSucc),
          T.vertex (Equiv.swap z o j.succ))
      have hjeq : j = ⟨1, by omega⟩ := Fin.ext hj1
      rw [hjeq, hedgeOne]
      apply (Sym2.eq_iff).2
      right
      constructor
      · congr 1 <;> simp [z, o, Equiv.swap_apply_def]
      · congr 1 <;> simp [z, o, Equiv.swap_apply_def]
    · have hj2 : 2 ≤ j.val := by omega
      change G.ends (T.edge j) =
        s(T.vertex (Equiv.swap z o j.castSucc),
          T.vertex (Equiv.swap z o j.succ))
      rw [hsuffix2.2.2 j hj2]
      congr 1
      · congr 1
        rw [hswapLater]
        change 2 ≤ j.val
        omega
      · congr 1
        rw [hswapLater]
        change 2 ≤ j.val + 1
        omega
  have hindexSLe : TashTreePathIndex G S ≤ 1 := by
    unfold TashTreePathIndex
    exact Nat.find_min' _ hsuffixS
  have hspecS : TashTreeSuffixPath G S (TashTreePathIndex G S) := by
    unfold TashTreePathIndex
    exact Nat.find_spec _
  have hindexS : TashTreePathIndex G S = 1 :=
    Nat.le_antisymm hindexSLe hspecS.1
  refine ⟨S, ⟨hlength, hedge, hvertexZero, hvertexOne, hvertexLater⟩,
    hbadS, ?_⟩
  left
  rw [hindexS, hq]
  omega
