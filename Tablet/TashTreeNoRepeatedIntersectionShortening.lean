import Tablet.ColoredVertexSetElementary
import Tablet.KTriple
import Tablet.TashTreeMinimumBadPair
import Tablet.TashTreeBadPair
import Tablet.TashTreePathIndex
import Tablet.TashTreeRankLess
import Tablet.TashTreeSuffixPath
import Tablet.TashkinovTree
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequencePreservesTashkinovTree
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentTashkinovSplice

-- [TABLET NODE: TashTreeNoRepeatedIntersectionShortening]
theorem TashTreeNoRepeatedIntersectionShortening {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : 2 < TashTreePathIndex G T)
    (hbefore : TashTreePathIndex G T < T.length)
    (beta epsilon : Fin k) (hne : epsilon ≠ beta)
    (i m : Fin (T.length + 1))
    (hi : i.val + 2 ≤ TashTreePathIndex G T)
    (hm : m.val + 2 ≤ TashTreePathIndex G T)
    (hbeta : beta ∈ MissingColors G phi (T.vertex i))
    (hlast : beta ∈
      MissingColors G phi (T.vertex (Fin.last T.length)))
    (hepsilon : epsilon ∈ MissingColors G phi (T.vertex m))
    (hmeets : ∃ s : Fin (T.length + 1),
      s.val + 1 ≤ TashTreePathIndex G T ∧
      Sum.inl (T.vertex s) ∈
        TwoColorComponent G phi epsilon beta
          (Sum.inl (T.vertex (Fin.last T.length)))) : False := by
-- BODY
  classical
  have hTashPrefix : ∀ (q : ℕ) (hq : 1 ≤ q) (hqT : q ≤ T.length),
      TashkinovTree G e0 phi (TreeSequencePrefix T q hq hqT) := by
    intro q hq hqT
    intro j hj
    rcases hmin.1.2.1 (Fin.castLE hqT j) hj with
      ⟨r, c, hcolor, hmissing⟩
    refine ⟨r, c, ?_, ?_⟩
    · exact hcolor
    · exact hmissing
  have hproper : IsProperEdgeColoring G phi := hmin.1.1.2.2.2.1
  by_cases hsmall : ∃ t : Fin (T.length + 1),
      t.val + 2 ≤ TashTreePathIndex G T ∧
        Sum.inl (T.vertex t) ∈ TwoColorComponent G phi epsilon beta
          (Sum.inl (T.vertex (Fin.last T.length)))
  · let S := TreeSequencePrefix T (TashTreePathIndex G T - 2) (by omega)
        (by omega)
    rcases hsmall with ⟨s, hs, hsm⟩
    have hq3 : 3 ≤ TashTreePathIndex G T := by omega
    have hqT : TashTreePathIndex G T - 2 ≤ T.length := by omega
    have hSlen : S.length = TashTreePathIndex G T - 2 := rfl
    have hiS : T.vertex i ∈ TreeSequenceVertexSet S := by
      rw [TreeSequenceVertexSet]
      refine Finset.mem_image.mpr ⟨Fin.castLT i (by omega),
        Finset.mem_univ _, ?_⟩
      rfl
    have hmS : T.vertex m ∈ TreeSequenceVertexSet S := by
      rw [TreeSequenceVertexSet]
      refine Finset.mem_image.mpr ⟨Fin.castLT m (by omega),
        Finset.mem_univ _, ?_⟩
      rfl
    have hlastOut : T.vertex (Fin.last T.length) ∉ TreeSequenceVertexSet S := by
      intro hlastIn
      rw [TreeSequenceVertexSet] at hlastIn
      rcases Finset.mem_image.mp hlastIn with ⟨j, hj, heq⟩
      have hv : (Fin.castLE (Nat.succ_le_succ hqT) j : Fin (T.length + 1)) =
          Fin.last T.length := by
        apply T.vertex_injective
        simpa [S, TreeSequencePrefix] using heq
      have hvval := congrArg Fin.val hv
      simp only [Fin.castLE, Fin.last] at hvval
      omega
    have hbetaS : beta ∈ TreeMissingColors phi S := by
      rw [TreeMissingColors]
      exact Finset.mem_biUnion.mpr ⟨T.vertex i, hiS, hbeta⟩
    have hepsilonS : epsilon ∈ TreeMissingColors phi S := by
      rw [TreeMissingColors]
      exact Finset.mem_biUnion.mpr ⟨T.vertex m, hmS, hepsilon⟩
    have hmeetS : ∃ u ∈ TreeSequenceVertexSet S,
        Sum.inl u ∈ TwoColorComponent G phi epsilon beta
          (Sum.inl (T.vertex (Fin.last T.length))) := by
      refine ⟨T.vertex s, ?_, hsm⟩
      rw [TreeSequenceVertexSet]
      refine Finset.mem_image.mpr ⟨Fin.castLT s (by omega),
        Finset.mem_univ _, ?_⟩
      rfl
    obtain ⟨u, S', hu, hucomp, hSS', hlength, haugment, hlastVertex, hsplice⟩ :=
      TwoColorComponentTashkinovSplice G phi S epsilon beta
        (T.vertex (Fin.last T.length)) hproper hne hepsilonS hbetaS
        hlastOut hmeetS
    have hTashS : TashkinovTree G e0 phi S := hTashPrefix _ (by omega) (by omega)
    have hTashS' := TashkinovAugmentationSequencePreservesTashkinovTree
      G e0 phi S S' hTashS haugment
    have hnotElementary : ¬ ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet S') := by
      intro he
      have hv' : T.vertex i ∈ TreeSequenceVertexSet S' := by
        rw [TreeSequenceVertexSet]
        let ii : Fin (S.length + 1) := Fin.castLT i (by omega)
        refine Finset.mem_image.mpr ⟨Fin.castLE (Nat.succ_le_succ hSS'.1) ii,
          Finset.mem_univ _, ?_⟩
        rw [hSS'.2.1]
        rfl
      have hy' : T.vertex (Fin.last T.length) ∈ TreeSequenceVertexSet S' := by
        rw [← hlastVertex, TreeSequenceVertexSet]
        exact Finset.mem_image.mpr ⟨Fin.last S'.length, Finset.mem_univ _, rfl⟩
      have hvne : T.vertex i ≠ T.vertex (Fin.last T.length) := by
        intro hvEq
        have hvEq' := T.vertex_injective hvEq
        have hvVal : i.val = T.length := by simpa using congrArg Fin.val hvEq'
        omega
      exact (Finset.disjoint_left.mp (he hv' hy' hvne)) hbeta hlast
    have hbad : TashTreeBadPair G k e0 phi S' := ⟨hmin.1.1, hTashS', hnotElementary⟩
    have hsuffix : TashTreeSuffixPath G S' (TashTreePathIndex G T - 1) := by
      refine ⟨by omega, by omega, ?_⟩
      intro r hr
      have hrbase : S.length ≤ r.val := by omega
      have hrne : r.val ≠ S.length := by omega
      have hrne' : r.val ≠ TashTreePathIndex G T - 2 := by omega
      simpa [hSlen, hrne'] using (hsplice r hrbase).2.2.2.2
    have hidx : TashTreePathIndex G S' ≤ TashTreePathIndex G T - 1 := by
      unfold TashTreePathIndex
      exact Nat.find_min' _ hsuffix
    apply (hmin.2 hbad)
    left
    omega
  · rcases hmeets with ⟨s, hs, hsm⟩
    have havoid : ∀ t : Fin (T.length + 1),
        t.val + 2 ≤ TashTreePathIndex G T →
        Sum.inl (T.vertex t) ∉ TwoColorComponent G phi epsilon beta
          (Sum.inl (T.vertex (Fin.last T.length))) := by
      intro t ht htc
      apply hsmall
      exact ⟨t, ht, htc⟩
    have hsLast : s.val + 1 = TashTreePathIndex G T := by
      have hqone : TashTreePathIndex G T - 1 + 1 = TashTreePathIndex G T := by omega
      have hsnot : ¬ s.val + 2 ≤ TashTreePathIndex G T := by
        intro hh
        exact havoid s hh hsm
      omega
    let S := TreeSequencePrefix T (TashTreePathIndex G T - 1) (by omega) (by omega)
    have hq3 : 3 ≤ TashTreePathIndex G T := by omega
    have hqT : TashTreePathIndex G T - 1 ≤ T.length := by omega
    have hiBound : i.val < S.length + 1 := by change i.val < TashTreePathIndex G T - 1 + 1; omega
    have hmBound : m.val < S.length + 1 := by change m.val < TashTreePathIndex G T - 1 + 1; omega
    have hsBound : s.val < S.length + 1 := by change s.val < TashTreePathIndex G T - 1 + 1; omega
    have hiS : T.vertex i ∈ TreeSequenceVertexSet S := by
      rw [TreeSequenceVertexSet]
      refine Finset.mem_image.mpr ⟨Fin.castLT i hiBound,
        Finset.mem_univ _, ?_⟩
      rfl
    have hmS : T.vertex m ∈ TreeSequenceVertexSet S := by
      rw [TreeSequenceVertexSet]
      refine Finset.mem_image.mpr ⟨Fin.castLT m hmBound,
        Finset.mem_univ _, ?_⟩
      rfl
    have hlastOut : T.vertex (Fin.last T.length) ∉ TreeSequenceVertexSet S := by
      intro hlastIn
      rw [TreeSequenceVertexSet] at hlastIn
      rcases Finset.mem_image.mp hlastIn with ⟨j, hj, heq⟩
      have hv : (Fin.castLE (Nat.succ_le_succ hqT) j : Fin (T.length + 1)) =
          Fin.last T.length := by
        apply T.vertex_injective
        simpa [S, TreeSequencePrefix] using heq
      have hvval := congrArg Fin.val hv
      simp only [Fin.castLE, Fin.last] at hvval
      omega
    have hbetaS : beta ∈ TreeMissingColors phi S := by
      rw [TreeMissingColors]
      exact Finset.mem_biUnion.mpr ⟨T.vertex i, hiS, hbeta⟩
    have hepsilonS : epsilon ∈ TreeMissingColors phi S := by
      rw [TreeMissingColors]
      exact Finset.mem_biUnion.mpr ⟨T.vertex m, hmS, hepsilon⟩
    have hmeetS : ∃ u ∈ TreeSequenceVertexSet S,
        Sum.inl u ∈ TwoColorComponent G phi epsilon beta
          (Sum.inl (T.vertex (Fin.last T.length))) := by
      refine ⟨T.vertex s, ?_, hsm⟩
      rw [TreeSequenceVertexSet]
      refine Finset.mem_image.mpr ⟨Fin.castLT s hsBound,
        Finset.mem_univ _, ?_⟩
      rfl
    obtain ⟨u, S', hu, hucomp, hSS', hlength, haugment, hlastVertex, hsplice⟩ :=
      TwoColorComponentTashkinovSplice G phi S epsilon beta
        (T.vertex (Fin.last T.length)) hproper hne hepsilonS hbetaS
        hlastOut hmeetS
    have hTashS : TashkinovTree G e0 phi S := hTashPrefix _ (by omega) (by omega)
    have hTashS' := TashkinovAugmentationSequencePreservesTashkinovTree
      G e0 phi S S' hTashS haugment
    have hbad : TashTreeBadPair G k e0 phi S' := by
      refine ⟨hmin.1.1, hTashS', ?_⟩
      intro he
      have hv' : T.vertex i ∈ TreeSequenceVertexSet S' := by
        rw [TreeSequenceVertexSet]
        let ii : Fin (S.length + 1) := Fin.castLT i (by omega)
        refine Finset.mem_image.mpr ⟨Fin.castLE (Nat.succ_le_succ hSS'.1) ii,
          Finset.mem_univ _, ?_⟩
        rw [hSS'.2.1]
        rfl
      have hy' : T.vertex (Fin.last T.length) ∈ TreeSequenceVertexSet S' := by
        rw [← hlastVertex, TreeSequenceVertexSet]
        exact Finset.mem_image.mpr ⟨Fin.last S'.length, Finset.mem_univ _, rfl⟩
      have hvne : T.vertex i ≠ T.vertex (Fin.last T.length) := by
        intro hvEq
        have hvEq' := T.vertex_injective hvEq
        have hvVal : i.val = T.length := by simpa using congrArg Fin.val hvEq'
        omega
      exact (Finset.disjoint_left.mp (he hv' hy' hvne)) hbeta hlast
    have huLast : u = S.vertex (Fin.last S.length) := by
      rw [TreeSequenceVertexSet] at hu
      rcases Finset.mem_image.mp hu with ⟨j, hj, hjEq⟩
      by_contra hneLast
      have hjne : j.val ≠ S.length := by
        intro heq
        apply hneLast
        rw [← hjEq]
        congr 1
        apply Fin.ext
        exact heq
      have hjbound : j.val + 2 ≤ TashTreePathIndex G T := by
        change j.val + 2 ≤ TashTreePathIndex G T
        have hjlt := j.isLt
        change j.val < TashTreePathIndex G T - 1 + 1 at hjlt
        have hqone : TashTreePathIndex G T - 1 + 1 = TashTreePathIndex G T := by omega
        rw [← hqone] at hjlt
        change j.val ≠ TashTreePathIndex G T - 1 at hjne
        omega
      apply havoid (Fin.castLT j (by change j.val < T.length + 1; omega)) hjbound
      rw [← hjEq] at hucomp
      simpa [S, TreeSequencePrefix, Fin.castLE, Fin.castLT] using hucomp
    have hsuffix : TashTreeSuffixPath G S' (TashTreePathIndex G T - 1) := by
      refine ⟨by omega, by omega, ?_⟩
      intro r hr
      have hrbase : S.length ≤ r.val := by
        change TashTreePathIndex G T - 1 ≤ r.val
        exact hr
      by_cases hrfirst : r.val = S.length
      · have hrEq : r.castSucc = Fin.castLE (Nat.succ_le_succ hSS'.1) (Fin.last S.length) := by
          apply Fin.ext
          simp only [Fin.castSucc, Fin.castLE, Fin.last]
          exact hrfirst
        have hfirst := (hsplice r hrbase).2.2.2.2
        rw [hrfirst] at hfirst
        have hvertex : S'.vertex r.castSucc = u := by
          rw [hrEq, hSS'.2.1, huLast]
        rw [hvertex]
        simpa [hrfirst] using hfirst
      · have hrne' : r.val ≠ TashTreePathIndex G T - 1 := by
          intro heq
          apply hrfirst
          change r.val = S.length
          exact heq
        simpa [hrne', hrfirst] using (hsplice r hrbase).2.2.2.2
    have hidx : TashTreePathIndex G S' ≤ TashTreePathIndex G T - 1 := by
      unfold TashTreePathIndex
      exact Nat.find_min' _ hsuffix
    apply (hmin.2 hbad)
    left
    omega
