import Tablet.OddCycleIn
import Tablet.ScheideMaximalKempePath

-- [TABLET NODE: ScheideMaximalOddCycle]
theorem ScheideMaximalOddCycle {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (htriple : KTriple G k e0 phi)
    (hmax : FixedPairMaximalTashkinovTree G e0 phi T) :
    OddCycleIn G (TreeSequenceVertexSet T) := by
-- BODY
  classical
  have hlenpos : 0 < T.length := lt_of_lt_of_le Nat.zero_lt_one T.positive
  have hTash : TashkinovTree G e0 phi T := hmax.1
  have hinc0 : Incident G (T.vertex ⟨0, Nat.succ_pos _⟩) e0 := by
    have h := T.attaches ⟨0, hlenpos⟩
    rw [T.first_edge] at h
    obtain ⟨i, hi⟩ := h
    have hi0 : i = ⟨0, Nat.succ_pos _⟩ := Fin.eq_zero i
    change T.vertex ⟨0, Nat.succ_pos _⟩ ∈ G.ends e0
    rw [hi]
    simp [Incident, hi0]
    right
    rfl
  have hinc1 : Incident G (T.vertex ⟨1, Nat.lt_succ_iff.mpr T.positive⟩) e0 := by
    obtain ⟨i, hi⟩ := T.attaches ⟨0, hlenpos⟩
    rw [T.first_edge] at hi
    change T.vertex ⟨1, Nat.lt_succ_iff.mpr T.positive⟩ ∈ G.ends e0
    rw [hi]
    simp [Incident]
  have hpresent_le : ∀ v, Incident G v e0 →
      (PresentColors G phi v).card ≤ (Finset.univ.filter (fun e => Incident G v e ∧ e ≠ e0)).card := by
    intro v he0
    let target : Finset E := Finset.univ.filter (fun e => Incident G v e ∧ e ≠ e0)
    let chooseEdge : Fin k → E := fun c => if hc : c ∈ PresentColors G phi v then
      Classical.choose (show ∃ e, Incident G v e ∧ phi e = some c by
        simpa [PresentColors] using hc) else e0
    have choose_mem : ∀ c, c ∈ PresentColors G phi v → chooseEdge c ∈ target := by
      intro c hc
      have hw := Classical.choose_spec (show ∃ e, Incident G v e ∧ phi e = some c by
        simpa [PresentColors] using hc)
      have hne0 : Classical.choose (show ∃ e, Incident G v e ∧ phi e = some c by
          simpa [PresentColors] using hc) ≠ e0 := by
        intro he
        subst he
        have hu := htriple.2.2.2.2.1
        rw [hu] at hw
        simp at hw
      have hne : chooseEdge c ≠ e0 := by simpa [chooseEdge, hc] using hne0
      have hinc : Incident G v (chooseEdge c) := by simpa [chooseEdge, hc] using hw.1
      change chooseEdge c ∈ target
      simp [target, hinc, hne]
    have choose_eq : ∀ c, c ∈ PresentColors G phi v →
        phi (chooseEdge c) = some c := by
      intro c hc
      have hh := Classical.choose_spec (show ∃ e, Incident G v e ∧ phi e = some c by
        simpa [PresentColors] using hc)
      simpa [chooseEdge, dif_pos hc] using hh.2
    apply Finset.card_le_card_of_injOn chooseEdge
    · intro c hc
      exact choose_mem c hc
    · intro a ha b hb hab
      have ea := choose_eq a ha
      have eb := choose_eq b hb
      rw [hab] at ea
      have heq : some a = some b := ea.symm.trans eb
      exact Option.some.inj heq
  have hmiss2 (v : V) (hv : Incident G v e0) :
      2 ≤ (MissingColors G phi v).card := by
    have hdeg : Degree G v ≤ MaximumDegree G := by
      change Degree G v ≤ (insert 0 (Finset.univ.image (fun w => Degree G w))).max' _
      exact Finset.le_max' (insert 0 (Finset.univ.image (fun w => Degree G w)))
        (Degree G v) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨v, by simp, rfl⟩))
    have hcard : (Finset.univ.filter (fun e => Incident G v e ∧ e ≠ e0)).card ≤ Degree G v - 1 := by
      have he : e0 ∈ Finset.univ.filter (fun e => Incident G v e) := by simp [hv]
      have hc := Finset.card_erase_add_one he
      have hsub : (Finset.univ.filter (fun e => Incident G v e ∧ e ≠ e0)) =
          (Finset.univ.filter (fun e => Incident G v e)).erase e0 := by
        ext e
        simp [hv, and_comm]
      rw [hsub]
      change ((Finset.univ.filter (fun e => Incident G v e)).erase e0).card ≤
        (Finset.univ.filter (fun e => Incident G v e)).card - 1
      omega
    have hp := hpresent_le v hv
    have hm : (MissingColors G phi v).card = k - (PresentColors G phi v).card := by
      simp [MissingColors, Finset.card_sdiff]
    have hk : MaximumDegree G + 1 ≤ k := htriple.2.2.1
    rw [hm]
    have hpk : (PresentColors G phi v).card ≤ Degree G v - 1 := hp.trans hcard
    have hdeg' : Degree G v + 1 ≤ MaximumDegree G + 1 := Nat.add_le_add_right hdeg 1
    have hdpos : 0 < Degree G v := by
      unfold Degree
      simp only [Finset.card_pos]
      exact ⟨e0, by simp [hv]⟩
    have hplt : (PresentColors G phi v).card < Degree G v :=
      (Nat.le_sub_one_iff_lt hdpos).mp hpk
    have hpk' : (PresentColors G phi v).card + 2 ≤ Degree G v + 1 := by omega
    have hkm : (PresentColors G phi v).card + 2 ≤ k :=
      le_trans hpk' (le_trans hdeg' hk)
    omega
  let x : V := T.vertex ⟨0, Nat.succ_pos _⟩
  let y : V := T.vertex ⟨1, Nat.lt_succ_iff.mpr T.positive⟩
  have hnonemptyx : (MissingColors G phi x).Nonempty := by
    exact Finset.card_pos.mp (by have := hmiss2 x hinc0; omega)
  have hnonemptyy : (MissingColors G phi y).Nonempty := by
    exact Finset.card_pos.mp (by have := hmiss2 y hinc1; omega)
  obtain ⟨alpha, halpha⟩ := hnonemptyx
  obtain ⟨beta, hbeta⟩ := hnonemptyy
  have hxy : x ≠ y := by
    intro h
    change T.vertex ⟨0, Nat.succ_pos _⟩ =
      T.vertex ⟨1, Nat.lt_succ_iff.mpr T.positive⟩ at h
    have hz : (⟨0, Nat.succ_pos _⟩ : Fin (T.length + 1)) =
        ⟨1, Nat.lt_succ_iff.mpr T.positive⟩ := T.vertex_injective h
    exact by simpa using congrArg Fin.val hz
  have hab : alpha ≠ beta := by
    have helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) :=
      (ScheideMaximalElementaryClosed G k e0 phi T htriple hmax).1
    have hxmem : x ∈ TreeSequenceVertexSet T := by
      simp [x, TreeSequenceVertexSet]
    have hymem : y ∈ TreeSequenceVertexSet T := by
      simp [y, TreeSequenceVertexSet]
    exact fun h => Finset.disjoint_left.mp (helem hxmem hymem hxy) halpha (h ▸ hbeta)
  obtain ⟨_, ⟨p, hp, hsupp, hlen, hverts, _⟩⟩ :=
    ScheideMaximalKempePath G k e0 phi T T htriple hmax hTash
      ⟨0, Nat.succ_pos _⟩ ⟨1, Nat.lt_succ_iff.mpr T.positive⟩ Nat.zero_lt_one alpha beta halpha hbeta
  unfold OddCycleIn
  obtain ⟨q, hq⟩ := hlen
  have hpar : ∀ {a b} (q0 : (TwoColorIncidenceGraph G phi alpha beta).Walk a b) (r : ℕ),
      r ≤ q0.length →
      ((∃ v, q0.getVert r = Sum.inl v) ↔
        Sum.rec (fun _ => Even r) (fun _ => Odd r) a) ∧
      ((∃ e, q0.getVert r = Sum.inr e) ↔
        Sum.rec (fun _ => Odd r) (fun _ => Even r) a) := by
    intro a b q0
    induction q0 with
    | @nil a =>
        intro r hr
        have : r = 0 := by simpa using hr
        subst r
        cases a <;> cases ‹V ⊕ E› <;> simp_all [SimpleGraph.Walk.getVert, Sum.exists]
    | @cons a b c hab tail ih =>
        intro r hr
        cases r with
        | zero => cases a <;> simp
        | succ r =>
            have hr' : r ≤ tail.length := by simp_all [SimpleGraph.Walk.length_cons]
            have hi := ih r hr'
            cases a <;> cases b
            all_goals try {exfalso; simpa [TwoColorIncidenceGraph] using hab}
            all_goals
              simp only [SimpleGraph.Walk.getVert_cons_succ]
              simpa [Nat.even_add_one, Nat.odd_add_one] using hi
  let n : ℕ := 2 * q + 1
  have hnpos : 0 < n := by simp [n]
  have hpn : p.length = 2 * (n - 1) := by
    simpa [n, Nat.add_sub_cancel, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hq
  let vertex : Fin n → V := fun i =>
    Classical.choose ((hpar p (2 * i.val) (by omega)).1.mpr (by simp))
  have vertex_spec : ∀ i : Fin n, p.getVert (2 * i.val) = Sum.inl (vertex i) := by
    intro i
    exact Classical.choose_spec ((hpar p (2 * i.val) (by omega)).1.mpr (by simp))
  let edge : Fin n → E := fun i =>
    if hi : i.val < n - 1 then
      Classical.choose ((hpar p (2 * i.val + 1) (by omega)).2.mpr (by simp))
    else e0
  have edge_spec : ∀ (i : Fin n), i.val < n - 1 →
      p.getVert (2 * i.val + 1) = Sum.inr (edge i) := by
    intro i hi
    simpa [edge, hi] using
      (Classical.choose_spec ((hpar p (2 * i.val + 1) (by omega)).2.mpr (by simp)))
  have vertex_mem : ∀ i : Fin n, vertex i ∈ TreeSequenceVertexSet T := by
    intro i
    apply hverts
    rw [← vertex_spec i]
    exact p.getVert_mem_support _
  have next_index : ∀ i : Fin n, i.val < n - 1 → i.val + 1 < n := by
    intro i hi
    have hle : i.val + 1 ≤ n - 1 := Nat.succ_le_iff.mpr hi
    have hlt : n - 1 < n := Nat.sub_lt hnpos (by omega)
    exact lt_of_le_of_lt hle hlt
  have edge_inc : ∀ (i : Fin n) (hi : i.val < n - 1),
      G.ends (edge i) = s(vertex i, vertex ⟨i.val + 1, next_index i hi⟩) := by
    intro i hi
    have hle : i.val + 1 ≤ n - 1 := Nat.succ_le_iff.mpr hi
    have hlt : n - 1 < n := Nat.sub_lt hnpos (by omega)
    have hnext : i.val + 1 < n := lt_of_le_of_lt hle hlt
    have hbound1 : 2 * (i.val + 1) ≤ p.length := by
      rw [hpn]
      exact Nat.mul_le_mul_left 2 hle
    have hbound0 : 2 * i.val ≤ p.length := by omega
    have ha := p.adj_getVert_succ (i := 2 * i.val) (by omega)
    have hb := p.adj_getVert_succ (i := 2 * i.val + 1) (by omega)
    rw [vertex_spec i, edge_spec i hi] at ha
    have hv : p.getVert (2 * (i.val + 1)) =
        Sum.inl (vertex ⟨i.val + 1, hnext⟩) := by
      convert vertex_spec ⟨i.val + 1, hnext⟩ using 1 <;> omega
    rw [edge_spec i hi] at hb
    have hbv : p.getVert (2 * i.val + 1 + 1) =
        Sum.inl (vertex ⟨i.val + 1, hnext⟩) := by
      simpa [Nat.mul_add, Nat.add_assoc] using hv
    rw [hbv] at hb
    have ha' : Incident G (vertex i) (edge i) := by
      have ha0 : Incident G (vertex i) (edge i) ∧
          (phi (edge i) = some alpha ∨ phi (edge i) = some beta) := by
        simpa [TwoColorIncidenceGraph] using ha
      exact ha0.1
    have hb' : Incident G (vertex ⟨i.val + 1, hnext⟩) (edge i) := by
      have hv : p.getVert (2 * (i.val + 1)) =
          Sum.inl (vertex ⟨i.val + 1, hnext⟩) := by
        convert vertex_spec ⟨i.val + 1, hnext⟩ using 1 <;> omega
      have hb0 : Incident G (vertex ⟨i.val + 1, hnext⟩) (edge i) ∧
          (phi (edge i) = some alpha ∨ phi (edge i) = some beta) := by
        simpa [TwoColorIncidenceGraph] using hb
      exact hb0.1
    have hne : vertex i ≠ vertex ⟨i.val + 1, hnext⟩ := by
      intro heq
      have he : p.getVert (2 * i.val) = p.getVert (2 * (i.val + 1)) := by
        rw [vertex_spec i, vertex_spec ⟨i.val + 1, hnext⟩, heq]
      have hi := hp.getVert_injOn hbound0 hbound1 he
      omega
    exact (Sym2.mem_and_mem_iff hne).mp ⟨ha', hb'⟩
  refine ⟨n, hnpos, vertex, edge, ?_, ?_, ?_, ?_, vertex_mem, ?_⟩
  · have hp0 : 0 < p.length := by
      by_contra hz
      have heq : p.length = 0 := Nat.eq_zero_of_not_pos hz
      have hends := p.eq_of_length_eq_zero heq
      exfalso
      apply hxy
      simpa [x, y] using hends
    omega
  · simp [n]
  · intro a b hab
    have ha1 : a.val ≤ n - 1 := (Nat.le_sub_one_iff_lt hnpos).mpr a.isLt
    have hb1 : b.val ≤ n - 1 := (Nat.le_sub_one_iff_lt hnpos).mpr b.isLt
    have ha2 : 2 * a.val ≤ p.length := by
      rw [hpn]
      exact Nat.mul_le_mul_left 2 ha1
    have hb2 : 2 * b.val ≤ p.length := by
      rw [hpn]
      exact Nat.mul_le_mul_left 2 hb1
    have hi := hp.getVert_injOn ha2 hb2 (by
      rw [vertex_spec a, vertex_spec b]
      exact congrArg Sum.inl hab)
    apply Fin.ext
    omega
  · intro a b hab
    by_cases ha : a.val < n - 1
    · by_cases hb : b.val < n - 1
      · have ea := edge_spec a ha
        have eb := edge_spec b hb
        have ha1 : a.val + 1 ≤ n - 1 := Nat.succ_le_iff.mpr ha
        have hb1 : b.val + 1 ≤ n - 1 := Nat.succ_le_iff.mpr hb
        have ha2 : 2 * a.val + 1 ≤ p.length := by
          rw [hpn]
          exact le_trans (by omega) (Nat.mul_le_mul_left 2 ha1)
        have hb2 : 2 * b.val + 1 ≤ p.length := by
          rw [hpn]
          exact le_trans (by omega) (Nat.mul_le_mul_left 2 hb1)
        have hget : p.getVert (2 * a.val + 1) = p.getVert (2 * b.val + 1) := by
          rw [ea, eb, hab]
        have hi' := hp.getVert_injOn ha2 hb2 hget
        apply Fin.ext
        omega
      · have he0 : phi e0 = none := htriple.2.2.2.2.1
        have heq : edge b = e0 := by simp [edge, hb]
        have hh : p.getVert (2 * a.val + 1) = Sum.inr e0 := by
          rw [edge_spec a ha, hab, heq]
        have hc := p.adj_getVert_succ (i := 2 * a.val) (by omega)
        rw [vertex_spec a, hh] at hc
        have hc' : phi e0 = some alpha ∨ phi e0 = some beta := by
          simpa [TwoColorIncidenceGraph] using hc.2
        simp [he0] at hc'
    · by_cases hb : b.val < n - 1
      · have he0 : phi e0 = none := htriple.2.2.2.2.1
        have ea := edge_spec b hb
        have heq : edge a = e0 := by simp [edge, ha]
        have hh : p.getVert (2 * b.val + 1) = Sum.inr e0 := by
          rw [ea, ← hab, heq]
        have hc := p.adj_getVert_succ (i := 2 * b.val) (by omega)
        rw [vertex_spec b, hh] at hc
        have hc' : phi e0 = some alpha ∨ phi e0 = some beta :=
          (by simpa [TwoColorIncidenceGraph] using hc.2)
        simp [he0] at hc'
      · have hab' : a.val = b.val := by omega
        exact Fin.ext hab'
  · intro i
    by_cases hi : i.val < n - 1
    · have hfi : (⟨(i.val + 1) % n, Nat.mod_lt _ hnpos⟩ : Fin n) =
          ⟨i.val + 1, next_index i hi⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt (next_index i hi)
      simpa only [hfi] using edge_inc i hi
    · have hi' : i.val = n - 1 := by omega
      have hi0 : i = ⟨n - 1, by omega⟩ := Fin.ext hi'
      rw [hi0]
      simp [edge]
      have hmod : ((n - 1 + 1) % n) = 0 := by
        have hn1 : 1 ≤ n := by omega
        have heq : n - 1 + 1 = n := Nat.sub_add_cancel hn1
        rw [heq]
        exact Nat.mod_self n
      simp only [hmod]
      have vlast : vertex ⟨n - 1, by omega⟩ = y := by
        have he := vertex_spec ⟨n - 1, by omega⟩
        rw [hpn.symm, p.getVert_length] at he
        exact Sum.inl.inj he.symm
      have vzero : vertex ⟨0, by omega⟩ = x := by
        have he := vertex_spec ⟨0, by omega⟩
        have hz : 2 * (⟨0, by omega⟩ : Fin n).val = 0 := by simp
        rw [hz, p.getVert_zero] at he
        change vertex ⟨0, by omega⟩ = T.vertex ⟨0, Nat.succ_pos _⟩
        exact Sum.inl.inj he.symm
      rw [vlast, vzero]
      exact (Sym2.mem_and_mem_iff hxy.symm).mp ⟨hinc1, hinc0⟩
