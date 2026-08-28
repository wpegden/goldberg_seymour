import Tablet.ScheideDefectiveChainBoundaryEdges
import Tablet.ScheideDepartureReturn

-- [TABLET NODE: ScheideDefectiveChainDepartureReturn]
theorem ScheideDefectiveChainDepartureReturn {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T)
    (alpha gamma : Fin k)
    (halpha : alpha ∈ DefectiveColors G phi (TreeSequenceVertexSet T))
    (hgammaFree : gamma ∈ TreeFreeColors phi T)
    (u : V) (hu : u ∈ TreeSequenceVertexSet T)
    (hgamma : gamma ∈ MissingColors G phi u)
    (z : V)
    (p : (TwoColorIncidenceGraph G phi alpha gamma).Walk
      (Sum.inl u) (Sum.inl z))
    (hp : ScheideDefectiveChainPath T phi alpha gamma u z p) :
    ∃ (i1 i2 : Fin (p.length + 1)) (v1 v2 : V),
      ScheideDepartureReturn T i1 i2 v1 v2 := by
-- BODY
  classical
  rcases hp with ⟨huT, hpath, hzout, hcomponent⟩
  have hp0 : ScheideDefectiveChainPath T phi alpha gamma u z p :=
    ⟨huT, hpath, hzout, hcomponent⟩
  let X := TreeSequenceVertexSet T
  let outside : Finset (Fin (p.length + 1)) :=
    Finset.univ.filter (fun i => ∃ v : V, p.getVert i.val = Sum.inl v ∧ v ∉ X)
  have hend : p.getVert p.length = Sum.inl z := by simp
  have hout : (Fin.last p.length) ∈ outside := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by simpa [hend, X] using hzout⟩
  let i1 := outside.min' (by exact ⟨Fin.last p.length, hout⟩)
  have hi1out : ∃ v : V, p.getVert i1.val = Sum.inl v ∧ v ∉ X := by
    exact (Finset.mem_filter.mp (Finset.min'_mem outside _)).2
  rcases hi1out with ⟨v1, hv1, hv1out⟩
  have hbefore : ∀ r : Fin (p.length + 1), r.val < i1.val →
      ∀ w : V, p.getVert r.val = Sum.inl w → w ∈ X := by
    intro r hr w hw
    by_contra hn
    have hm : r ∈ outside := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, ⟨w, hw, hn⟩⟩
    have hmin := Finset.min'_le outside r hm
    exact (Nat.not_lt_of_ge hmin) hr
  have hfacts := ScheideGlobalMaximumBoundaryFacts G k e0 phi T hglobal
  have hcard : 3 ≤ (BoundaryColorEdges G phi X alpha).card := by
    exact (hfacts.2.2 alpha halpha).2
  let B := BoundaryColorEdges G phi X alpha
  have hbcard : 3 ≤ B.card := by simpa [B, X] using hcard
  have hbpos : B.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨f1, hf1⟩ := hbpos
  obtain ⟨f2, hf2, hf12⟩ := B.exists_mem_ne (by omega) f1
  have hcard2 : 2 ≤ (B.erase f1).card := by
    rw [Finset.card_erase_of_mem hf1]
    omega
  obtain ⟨f3, hf3, hf23⟩ := (B.erase f1).exists_mem_ne (by omega) f2
  have hf31 : f3 ≠ f1 := by
    intro h
    subst h
    simp at hf3
  have edge_occurrence : ∀ f ∈ B, ∃ n ≤ p.length, p.getVert n = Sum.inr f := by
    intro f hf
    have hs : Sum.inr f ∈ p.support := by
      have hh := (ScheideDefectiveChainBoundaryEdges G k e0 phi T hglobal
        alpha gamma halpha hgammaFree u hu hgamma z p hp0) f
      exact (hh.mp (by simpa [B] using hf)).2
    rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hs with ⟨n, hn, hnl⟩
    exact ⟨n, hnl, hn⟩
  obtain ⟨n1, hn1, he1⟩ := edge_occurrence f1 hf1
  obtain ⟨n2, hn2, he2⟩ := edge_occurrence f2 hf2
  obtain ⟨n3, hn3, he3⟩ := edge_occurrence f3 (Finset.mem_of_mem_erase hf3)
  have edge_has_neighbor : ∀ f ∈ B, ∀ n ≤ p.length, p.getVert n = Sum.inr f →
      ∃ j v, j ≤ p.length ∧ (j + 1 = n ∨ n + 1 = j) ∧
        p.getVert j = Sum.inl v ∧ v ∈ X := by
    intro f hf n hnl he
    have hn0 : 0 < n := by
      by_contra hn
      have : n = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_not_gt hn)
      subst this
      simp at he
    have hnlast : n < p.length := by
      by_contra h
      have heq := p.getVert_of_length_le (i := n) (by omega)
      rw [he] at heq
      simp at heq
    have hleft := p.adj_getVert_succ (i := n - 1) (by omega)
    have hright := p.adj_getVert_succ (i := n) (by omega)
    have hfboundary : f ∈ BoundaryEdges G X := by
      have hfboth : f ∈ BoundaryEdges G X ∧ phi f = some alpha := by
        simpa [B, BoundaryColorEdges] using hf
      exact hfboth.1
    simp [BoundaryEdges] at hfboundary
    rcases hfboundary with ⟨a, ha, b, hb, hends⟩
    have hleft' : (TwoColorIncidenceGraph G phi alpha gamma).Adj
        (p.getVert (n - 1)) (p.getVert n) := by
      have hindex : n - 1 + 1 = n := by omega
      simpa [hindex] using hleft
    rw [he] at hleft' hright
    cases hl : p.getVert (n - 1) with
    | inl vl =>
      cases hr : p.getVert (n + 1) with
      | inl vr =>
        rw [hl] at hleft'
        rw [hr] at hright
        simp [TwoColorIncidenceGraph] at hleft'
        simp [TwoColorIncidenceGraph] at hright
        simp [Incident] at hleft' hright
        rw [hends] at hleft' hright
        simp at hleft' hright
        by_cases hvl : vl ∈ X
        · exact ⟨n - 1, vl, by omega, by omega, hl, hvl⟩
        by_cases hvr : vr ∈ X
        · exact ⟨n + 1, vr, by omega, by omega, hr, hvr⟩
        rcases hleft' with hleft' | hleft' <;>
          rcases hright.1 with hright' | hright' <;>
          simp_all
        all_goals
          have heqpath : n - 1 = n + 1 := hpath.getVert_injOn
            (by simp; omega) (by simp; omega) (by simpa [hl, hr])
          omega
      | inr er =>
        rw [hr] at hright
        exfalso
        simp [TwoColorIncidenceGraph] at hright
    | inr el =>
      rw [hl] at hleft'
      exfalso
      simp [TwoColorIncidenceGraph] at hleft'
  have edge_before : ∀ f ∈ B, ∀ n ≤ p.length, p.getVert n = Sum.inr f →
      n < i1.val → n + 1 = i1.val := by
    intro f hf n hnl he hnfirst
    have hn0 : 0 < n := by
      by_contra hn
      have heq : n = 0 := by omega
      subst heq
      simp at he
    have hnlast : n < p.length := by
      by_contra h
      have heq := p.getVert_of_length_le (i := n) (by omega)
      rw [he] at heq
      simp at heq
    have hleft := p.adj_getVert_succ (i := n - 1) (by omega)
    have hright := p.adj_getVert_succ (i := n) (by omega)
    have hleft' : (TwoColorIncidenceGraph G phi alpha gamma).Adj
        (p.getVert (n - 1)) (p.getVert n) := by
      have hindex : n - 1 + 1 = n := by omega
      simpa [hindex] using hleft
    rw [he] at hleft' hright
    have hfboundary : f ∈ BoundaryEdges G X := by
      have hfboth : f ∈ BoundaryEdges G X ∧ phi f = some alpha := by
        simpa [B, BoundaryColorEdges] using hf
      exact hfboth.1
    simp [BoundaryEdges] at hfboundary
    rcases hfboundary with ⟨a, ha, b, hb, hends⟩
    cases hl : p.getVert (n - 1) with
    | inl vl =>
      cases hr : p.getVert (n + 1) with
      | inl vr =>
        rw [hl] at hleft'
        rw [hr] at hright
        simp [TwoColorIncidenceGraph, Incident] at hleft' hright
        rw [hends] at hleft' hright
        simp at hleft' hright
        by_cases heq : n + 1 = i1.val
        · exact heq
        have hvlX : vl ∈ X := by
          apply hbefore ⟨n - 1, by omega⟩ (by omega : n - 1 < i1.val)
          exact hl
        have hvrX : vr ∈ X := by
          apply hbefore ⟨n + 1, by omega⟩ (by omega : n + 1 < i1.val)
          exact hr
        rcases hleft' with hleft' | hleft' <;>
          rcases hright.1 with hright' | hright' <;>
          simp_all
        all_goals
          have heqpath : n - 1 = n + 1 := hpath.getVert_injOn
            (by simp; omega) (by simp; omega) (by simpa [hl, hr])
          omega
      | inr er =>
        rw [hr] at hright
        simp [TwoColorIncidenceGraph] at hright
    | inr el =>
      rw [hl] at hleft'
      simp [TwoColorIncidenceGraph] at hleft'
  have hn12 : n1 ≠ n2 := by
    intro heq
    apply hf12
    exact Sum.inr.inj (by rw [← he1, ← he2, heq])
  have hn13 : n1 ≠ n3 := by
    intro heq
    apply hf31
    exact Sum.inr.inj (by rw [← he1, ← he3, heq])
  have hn23 : n2 ≠ n3 := by
    intro heq
    apply hf23
    exact Sum.inr.inj (by rw [← he2, ← he3, heq])
  have hlater : ∃ n ∈ [n1, n2, n3], i1.val < n := by
    by_contra hn
    push_neg at hn
    have hle1 : n1 ≤ i1.val := hn n1 (by simp)
    have hle2 : n2 ≤ i1.val := hn n2 (by simp)
    have hle3 : n3 ≤ i1.val := hn n3 (by simp)
    have hne1 : n1 ≠ i1.val := by
      intro heq
      have hbad : Sum.inl v1 = Sum.inr f1 := by
        calc
          Sum.inl v1 = p.getVert i1.val := hv1.symm
          _ = p.getVert n1 := by rw [heq]
          _ = Sum.inr f1 := he1
      simp at hbad
    have hne2 : n2 ≠ i1.val := by
      intro heq
      have hbad : Sum.inl v1 = Sum.inr f2 := by
        calc
          Sum.inl v1 = p.getVert i1.val := hv1.symm
          _ = p.getVert n2 := by rw [heq]
          _ = Sum.inr f2 := he2
      simp at hbad
    have hne3 : n3 ≠ i1.val := by
      intro heq
      have hbad : Sum.inl v1 = Sum.inr f3 := by
        calc
          Sum.inl v1 = p.getVert i1.val := hv1.symm
          _ = p.getVert n3 := by rw [heq]
          _ = Sum.inr f3 := he3
      simp at hbad
    have hb1 := edge_before f1 hf1 n1 hn1 he1 (by omega)
    have hb2 := edge_before f2 hf2 n2 hn2 he2 (by omega)
    have hb3 := edge_before f3 (Finset.mem_of_mem_erase hf3) n3 hn3 he3 (by omega)
    omega
  rcases hlater with ⟨nret, hnret, hnretlater⟩
  have hnretB : ∃ f ∈ B, ∃ n ≤ p.length, p.getVert n = Sum.inr f ∧
      i1.val < n := by
    rcases (show nret = n1 ∨ nret = n2 ∨ nret = n3 by simpa using hnret) with h | h | h
    · subst nret
      exact ⟨f1, hf1, n1, hn1, he1, hnretlater⟩
    · subst nret
      exact ⟨f2, hf2, n2, hn2, he2, hnretlater⟩
    · subst nret
      exact ⟨f3, Finset.mem_of_mem_erase hf3, n3, hn3, he3, hnretlater⟩
  rcases hnretB with ⟨f, hf, n, hn, he, hnretlater⟩
  rcases edge_has_neighbor f hf n hn he with ⟨j, v, hjbound, hjrel, hjv, hvX⟩
  have hjlater : i1.val < j := by
    by_contra hnot
    have hjle : j ≤ i1.val := by omega
    rcases hjrel with hjn | hnj
    · by_cases hjeq : j = i1.val
      · have hvEq : v = v1 := by
          apply Sum.inl.inj
          calc
            Sum.inl v = p.getVert j := hjv.symm
            _ = p.getVert i1.val := by rw [hjeq]
            _ = Sum.inl v1 := hv1
        subst v
        exact hv1out hvX
      · have hjlt : j < i1.val := by omega
        omega
    · omega
  let returns : Finset (Fin (p.length + 1)) :=
    Finset.univ.filter (fun r => i1.val < r.val ∧
      ∃ w : V, p.getVert r.val = Sum.inl w ∧ w ∈ X)
  have hjmem : (⟨j, by omega⟩ : Fin (p.length + 1)) ∈ returns := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hjlater, ⟨v, hjv, hvX⟩⟩
  let i2 := returns.max' (by exact ⟨⟨j, by omega⟩, hjmem⟩)
  have hi2mem : i2 ∈ returns := Finset.max'_mem returns _
  rcases (Finset.mem_filter.mp hi2mem).2 with ⟨hi2later, v2, hv2, hv2X⟩
  have hafter : ∀ r : Fin (p.length + 1), i2.val < r.val →
      ∀ w : V, p.getVert r.val = Sum.inl w → w ∉ X := by
    intro r hri w hwr hwX
    have hrmem : r ∈ returns := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by omega, ⟨w, hwr, hwX⟩⟩
    have hrle := Finset.le_max' returns r hrmem
    omega
  refine ⟨i1, i2, v1, v2, ?_⟩
  exact ⟨hp0, hv1, hv1out, hbefore, hi2later, hv2, hv2X, hafter⟩
