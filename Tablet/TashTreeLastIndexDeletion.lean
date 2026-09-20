import Tablet.ColoredVertexSetElementary
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.TashTreeBadPair
import Tablet.TashTreeMinimumBadPair
import Tablet.TashTreePathIndex
import Tablet.TashTreeRankLess
import Tablet.TashTreeSuffixPath
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: TashTreeLastIndexDeletion]
theorem TashTreeLastIndexDeletion {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : 2 < TashTreePathIndex G T)
    (hlast : TashTreePathIndex G T = T.length)
    (gamma beta : Fin k) (r : Fin T.length) (p j : Fin (T.length + 1))
    (hr : r.val + 1 = T.length) (hp : p.val + 1 = T.length)
    (hj : j.val + 2 ≤ T.length)
    (hrgamma : phi (T.edge r) = some gamma)
    (hpgamma : gamma ∈ PresentColors G phi (T.vertex p))
    (hbj : beta ∈ MissingColors G phi (T.vertex j))
    (hblast : beta ∈ MissingColors G phi (T.vertex (Fin.last T.length))) :
    ∃ (P S : TreeSequence G e0) (s : Fin S.length),
      P.length + 2 = T.length ∧
        TreeSequenceInitialSegment P T ∧
        S.length = P.length + 1 ∧
        TreeSequenceInitialSegment P S ∧
        s.val + 1 = S.length ∧
        S.edge s = T.edge r ∧
        S.vertex (Fin.last S.length) = T.vertex (Fin.last T.length) ∧
        TashTreeBadPair G k e0 phi S ∧
        TashTreeRankLess G S T := by
-- BODY
  classical
  open scoped Sym2 in
   
  have hlen : 3 ≤ T.length := by omega
  have hqspec : TashTreeSuffixPath G T (TashTreePathIndex G T) := by
    unfold TashTreePathIndex
    exact Nat.find_spec _
  have hindex : TashTreePathIndex G T = T.length := hlast
  have hnotlast : ∀ i : Fin T.length, i.val ≠ T.length - 1 →
      i.val < T.length - 1 := by
    intro i hi
    omega
  have hrval : r.val = T.length - 1 := by omega
  have hrlast : r = ⟨T.length - 1, by omega⟩ := Fin.ext hrval
  let P : TreeSequence G e0 :=
    { length := T.length - 2
      positive := by omega
      vertex := fun i => T.vertex ⟨i.val, by omega⟩
      edge := fun i => T.edge ⟨i.val, by omega⟩
      vertex_injective := by
        intro a b hab
        apply Fin.ext
        simpa using congrArg Fin.val (T.vertex_injective hab)
      edge_injective := by
        intro a b hab
        apply Fin.ext
        simpa using congrArg Fin.val (T.edge_injective hab)
      first_edge := by
        rw [T.first_edge]
      attaches := by
        intro j
        let jj : Fin T.length := ⟨j.val, by omega⟩
        rcases T.attaches jj with ⟨i, hi⟩
        let ii : Fin (j.val + 1) := ⟨i.val, by simpa [jj] using i.isLt⟩
        refine ⟨ii, ?_⟩
        rw [hi]
        apply congrArg₂ Sym2.mk
        · congr 1
        · congr 1 } 
  have hattachLast : ∃ i : Fin (T.length - 1),
      G.ends (T.edge ⟨T.length - 1, by omega⟩) =
        Sym2.mk (T.vertex (Fin.last T.length))
          (T.vertex (Fin.castLT i (by omega))) := by
    rcases T.attaches ⟨T.length - 1, by omega⟩ with ⟨i, hi⟩
    have hineq : i.val ≠ T.length - 1 := by
      intro heq
      have heqi : i = ⟨T.length - 1, by omega⟩ := Fin.ext heq
      have hbad : TashTreeSuffixPath G T (T.length - 1) := by
        refine ⟨by omega, by omega, ?_⟩
        intro t ht
        have htval : t.val = T.length - 1 := by omega
        have hteq : t = ⟨T.length - 1, by omega⟩ := Fin.ext htval
        rw [hteq]
        have hi' := hi
        rw [heqi] at hi'
        rw [hi']
        apply Sym2.eq_iff.mpr
        right
        constructor <;> rfl
      have hle : TashTreePathIndex G T ≤ T.length - 1 := by
        unfold TashTreePathIndex
        exact Nat.find_min' _ hbad
      omega
    have hilt : i.val < T.length - 1 := by omega
    refine ⟨⟨i.val, hilt⟩, ?_⟩
    rw [hi]
    apply Sym2.eq_iff.mpr
    left
    constructor
    · apply congrArg T.vertex
      apply Fin.ext
      exact Nat.sub_add_cancel (by omega)
    · apply congrArg T.vertex
      apply Fin.ext
      rfl
  let svertex : Fin (T.length - 1 + 1) → V := fun i =>
    if hi : i.val < T.length - 1 then T.vertex ⟨i.val, by omega⟩
    else T.vertex (Fin.last T.length)
  let sedge : Fin (T.length - 1) → E := fun i =>
    if hi : i.val < T.length - 2 then T.edge ⟨i.val, by omega⟩
    else T.edge ⟨T.length - 1, by omega⟩
  let S : TreeSequence G e0 :=
    { length := T.length - 1
      positive := by omega
      vertex := svertex
      edge := sedge
      vertex_injective := by
        intro a b hab
        by_cases ha : a.val < T.length - 1
        · by_cases hb : b.val < T.length - 1
          · apply Fin.ext
            simpa using congrArg Fin.val (T.vertex_injective (by simpa [svertex, ha, hb] using hab))
          · have hbv : svertex b = T.vertex (Fin.last T.length) := by simp [svertex, hb]
            have hav : svertex a = T.vertex ⟨a.val, by omega⟩ := by simp [svertex, ha]
            have heq : T.vertex ⟨a.val, by omega⟩ = T.vertex (Fin.last T.length) := by
              simpa [hav, hbv] using hab
            have hv := T.vertex_injective heq
            have hval : a.val = T.length := by simpa using congrArg Fin.val hv
            omega
        · by_cases hb : b.val < T.length - 1
          · have hav : svertex a = T.vertex (Fin.last T.length) := by simp [svertex, ha]
            have hbv : svertex b = T.vertex ⟨b.val, by omega⟩ := by simp [svertex, hb]
            have heq : T.vertex (Fin.last T.length) = T.vertex ⟨b.val, by omega⟩ := by
              simpa [hav, hbv] using hab
            have hv := T.vertex_injective heq
            have hval : T.length = b.val := by simpa using congrArg Fin.val hv
            omega
          · apply Fin.ext
            omega
      edge_injective := by
        intro a b hab
        by_cases ha : a.val < T.length - 2
        · by_cases hb : b.val < T.length - 2
          · apply Fin.ext
            simpa using congrArg Fin.val (T.edge_injective (by simpa [sedge, ha, hb] using hab))
          · have hbe : sedge b = T.edge ⟨T.length - 1, by omega⟩ := by simp [sedge, hb]
            have hae : sedge a = T.edge ⟨a.val, by omega⟩ := by simp [sedge, ha]
            have heq : T.edge ⟨a.val, by omega⟩ = T.edge ⟨T.length - 1, by omega⟩ := by
              simpa [hae, hbe] using hab
            have hv := T.edge_injective heq
            have hval : a.val = T.length - 1 := by simpa using congrArg Fin.val hv
            omega
        · by_cases hb : b.val < T.length - 2
          · have hae : sedge a = T.edge ⟨T.length - 1, by omega⟩ := by simp [sedge, ha]
            have hbe : sedge b = T.edge ⟨b.val, by omega⟩ := by simp [sedge, hb]
            have heq : T.edge ⟨T.length - 1, by omega⟩ = T.edge ⟨b.val, by omega⟩ := by
              simpa [hae, hbe] using hab
            have hv := T.edge_injective heq
            have hval : T.length - 1 = b.val := by simpa using congrArg Fin.val hv
            omega
          · apply Fin.ext
            omega
      first_edge := by
        have hh : 0 < T.length - 2 := by omega
        simp [sedge, hh, T.first_edge]
      attaches := by
        intro j
        by_cases hj : j.val < T.length - 2
        · let jj : Fin T.length := ⟨j.val, by omega⟩
          rcases T.attaches jj with ⟨i, hi⟩
          let ii : Fin (j.val + 1) := ⟨i.val, by simpa [jj] using i.isLt⟩
          refine ⟨ii, ?_⟩
          have hjv : j.val + 1 < T.length - 1 := by omega
          have hiiv : ii.val < T.length - 1 := by dsimp [ii]; omega
          have hjj : jj = ⟨j.val, by omega⟩ := rfl
          simp only [sedge, dif_pos hj]
          change G.ends (T.edge ⟨j.val, by omega⟩) = _
          rw [show svertex j.succ = T.vertex jj.succ by
            simp [svertex, hjv]; congr 1]
          rw [show svertex (Fin.castLT ii (by omega)) = T.vertex (i.castLT (by omega)) by
            simp [svertex, hiiv]; congr 1]
          rw [hi]
        · rcases hattachLast with ⟨i, hi⟩
          let ii : Fin (j.val + 1) := ⟨i.val, by omega⟩
          refine ⟨ii, ?_⟩
          have hjv : j.val + 1 = T.length - 1 := by omega
          have hiiv : ii.val < T.length - 1 := by dsimp [ii]; omega
          rw [show sedge j = T.edge ⟨T.length - 1, by omega⟩ by simp [sedge, hj]]
          rw [show svertex j.succ = T.vertex (Fin.last T.length) by
            simp [svertex, hjv]]
          rw [show svertex (Fin.castLT ii (by omega)) = T.vertex (i.castLT (by omega)) by
            simp [svertex, hiiv]; congr 1]
          exact hi }
  have hPprefix : TreeSequenceInitialSegment P T := by
    refine ⟨by dsimp [P]; omega, ?_, ?_⟩
    · intro i
      rfl
    · intro i
      rfl
  have hPSegment : TreeSequenceInitialSegment P S := by
    refine ⟨by dsimp [P, S]; omega, ?_, ?_⟩
    · intro i
      dsimp [P, S, svertex, sedge]
      have hi' : i.val < P.length + 1 := i.isLt
      have hi : i.val < T.length - 1 := by
        dsimp [P] at hi'
        omega
      simp [hi]
    · intro i
      dsimp [P, S, svertex, sedge]
      have hi' : i.val < P.length := i.isLt
      have hi : i.val < T.length - 2 := by
        dsimp [P] at hi'
        omega
      simp [hi]
  have hTashS : TashkinovTree G e0 phi S := by
    intro q hqpos
    by_cases hqold : q.val < T.length - 2
    · have hT := hmin.1.2.1 ⟨q.val, by omega⟩ hqpos
      rcases hT with ⟨i, c, hc, hm⟩
      let u : Fin (q.val + 1) := ⟨i.val, by simpa using i.isLt⟩
      refine ⟨u, c, ?_, ?_⟩
      · have heq : sedge q = T.edge ⟨q.val, by omega⟩ := by simp [sedge, hqold]
        change phi (sedge q) = some c
        rw [heq]
        simpa using hc
      · have hiq : i.val < q.val + 1 := i.isLt
        have hiold : q.val < T.length - 2 := hqold
        have hi : i.val < T.length - 1 := by omega
        have hvi : S.vertex (Fin.castLT u (by omega)) =
            T.vertex (i.castLT (by omega)) := by
          dsimp [S, u]
          simp [svertex, hi]
          apply congrArg T.vertex
          apply Fin.ext
          rfl
        change c ∈ MissingColors G phi
          (S.vertex (Fin.castLT u (by omega)))
        rw [hvi]
        exact hm
    · have hqb : q.val < T.length - 1 := by
        have hh := q.isLt
        dsimp [S] at hh
        exact hh
      have hqval : q.val = T.length - 2 := by omega
      have hT := hmin.1.2.1 ⟨T.length - 1, by omega⟩ (by omega)
      rcases hT with ⟨i, c, hc, hm⟩
      have hcg : c = gamma := by
        apply Option.some.inj
        exact hc.symm.trans (hrlast ▸ hrgamma)
      subst c
      have hilast : i.val ≠ T.length - 1 := by
        intro hi
        have hii : T.vertex (Fin.castLT i (by omega)) = T.vertex p := by
          apply congrArg T.vertex
          apply Fin.ext
          have := hi
          have hpval : p.val = T.length - 1 := by omega
          simpa [hpval] using this
        have hmiss : gamma ∉ PresentColors G phi (T.vertex p) := by
          rw [← hii]
          simpa [MissingColors] using hm
        exact hmiss (hii ▸ hpgamma)
      let u : Fin (q.val + 1) := ⟨i.val, by omega⟩
      refine ⟨u, gamma, ?_, ?_⟩
      · have heq : sedge q = T.edge ⟨T.length - 1, by omega⟩ := by
          simp [sedge, hqval]
        change phi (sedge q) = some gamma
        rw [heq]
        exact hc
      · have hiil : i.val < T.length - 1 := by omega
        have hvi : S.vertex (Fin.castLT u (by omega)) =
            T.vertex (i.castLT (by omega)) := by
          dsimp [S, u]
          simp [svertex, hiil]
          apply congrArg T.vertex
          apply Fin.ext
          rfl
        change gamma ∈ MissingColors G phi
          (S.vertex (Fin.castLT u (by omega)))
        rw [hvi]
        exact hm
  have hnotElem : ¬ ColoredVertexSetElementary G phi (TreeSequenceVertexSet S) := by
    intro he
    have hjmem : T.vertex ⟨j.val, by omega⟩ ∈ TreeSequenceVertexSet S := by
      rw [TreeSequenceVertexSet]
      have hjS : j.val < S.length + 1 := by
        dsimp [S]
        omega
      refine Finset.mem_image.mpr ⟨⟨j.val, hjS⟩, Finset.mem_univ _, ?_⟩
      have hvj : svertex ⟨j.val, by omega⟩ = T.vertex ⟨j.val, by omega⟩ := by
        simp [svertex, show j.val < T.length - 1 by omega]
      exact hvj
    have hlmem : T.vertex (Fin.last T.length) ∈ TreeSequenceVertexSet S := by
      rw [TreeSequenceVertexSet]
      have hlastS : T.length - 1 < S.length + 1 := by
        dsimp [S]
        omega
      refine Finset.mem_image.mpr ⟨⟨T.length - 1, hlastS⟩, Finset.mem_univ _, ?_⟩
      simp [S, svertex]
    have hvne : T.vertex ⟨j.val, by omega⟩ ≠ T.vertex (Fin.last T.length) := by
      intro hh
      have hv := T.vertex_injective hh
      have hval : j.val = T.length := by
        simpa using congrArg Fin.val hv
      omega
    have hd := he hjmem hlmem hvne
    rw [Finset.disjoint_left] at hd
    exact hd (by simpa using hbj) (by simpa using hblast)
  have hbadS : TashTreeBadPair G k e0 phi S :=
    ⟨hmin.1.1, hTashS, hnotElem⟩
  have hindexS : TashTreePathIndex G S ≤ S.length := by
    have hs := (show TashTreeSuffixPath G S (TashTreePathIndex G S) by
      unfold TashTreePathIndex
      exact Nat.find_spec _)
    exact hs.2.1
  have hrank : TashTreeRankLess G S T := by
    left
    rw [hlast]
    have hslt : S.length < T.length := by dsimp [S]; omega
    exact lt_of_le_of_lt hindexS hslt
  have hsindex : T.length - 2 < S.length := by
    dsimp [S]
    omega
  refine ⟨P, S, ⟨T.length - 2, hsindex⟩, ?_⟩
  refine ⟨by dsimp [P]; omega, hPprefix, by dsimp [P, S]; omega,
    hPSegment, ?_, ?_, ?_, hbadS, hrank⟩
  · dsimp [S]
    omega
  · simp [S, sedge, hrlast]
  · simp [S, svertex]
