import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.ScheideReversedPathCertificate
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ScheideReversedKempePathTree]
theorem ScheideReversedKempePathTree {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (htriple : KTriple G k e0 phi)
    (alpha beta : Fin k)
    (halpha : alpha ∈ MissingColors G phi
      (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩))
    (hbeta : beta ∈ MissingColors G phi
      (T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩))
    (p : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩))
      (Sum.inl (T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩)))
    (hp : p.IsPath) (hdiv : 4 ∣ p.length) :
    Nonempty (ScheideReversedPathCertificate G k e0 phi T alpha beta p) := by
-- BODY
  classical
  obtain ⟨d, hd⟩ := hdiv
  have hlen : p.length = 4 * d := by omega
  have hparity : ∀ n ≤ p.length,
      (n % 2 = 0 → ∃ v, p.getVert n = Sum.inl v) ∧
      (n % 2 = 1 → ∃ e, p.getVert n = Sum.inr e) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      constructor
      · intro he
        by_cases hn0 : n = 0
        · exact ⟨T.vertex ⟨0, Nat.zero_lt_succ T.length⟩, by simpa [hn0] using p.getVert_zero⟩
        · obtain ⟨w, hz⟩ := (ih (n - 1) (by omega) (by omega)).2 (by omega)
          have ha := p.adj_getVert_succ (i := n - 1) (by omega)
          have hn' : n - 1 + 1 = n := by omega
          rw [hn'] at ha
          rw [hz] at ha
          cases hc : p.getVert n with
          | inl v => exact ⟨v, rfl⟩
          | inr e =>
              exfalso
              have ha' : (TwoColorIncidenceGraph G phi alpha beta).Adj
                  (Sum.inr w) (Sum.inr e) := hc ▸ ha
              simpa [TwoColorIncidenceGraph] using ha'
      · intro ho
        obtain ⟨w, hz⟩ := (ih (n - 1) (by omega) (by omega)).1 (by omega)
        have ha := p.adj_getVert_succ (i := n - 1) (by omega)
        have hn' : n - 1 + 1 = n := by omega
        rw [hn'] at ha
        rw [hz] at ha
        cases hc : p.getVert n with
        | inl v =>
            exfalso
            have ha' : (TwoColorIncidenceGraph G phi alpha beta).Adj
                (Sum.inl w) (Sum.inl v) := hc ▸ ha
            simpa [TwoColorIncidenceGraph] using ha'
        | inr e => exact ⟨e, rfl⟩
  let m := p.length / 2
  have hm : p.length = 2 * m := by omega
  have hends : T.vertex ⟨0, Nat.zero_lt_succ T.length⟩ ≠
      T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩ := by
    intro h
    have hne : (⟨0, Nat.zero_lt_succ T.length⟩ : Fin (T.length + 1)) ≠
        ⟨1, Nat.succ_lt_succ T.positive⟩ := by
      intro heq
      have hv := congrArg Fin.val heq
      norm_num at hv
    exact hne (T.vertex_injective h)
  have hpos : 0 < p.length := by
    by_contra hz
    have hz0 : p.length = 0 := Nat.eq_zero_of_not_pos hz
    have heq := SimpleGraph.Walk.eq_of_length_eq_zero hz0
    apply hends
    simpa using heq
  have hmpos : 2 ≤ m := by omega
  let vertexAt : Fin (m + 1) → V := fun i =>
    Classical.choose ((hparity (2 * i.val) (by omega)).1 (by omega))
  have vertexAt_eq : ∀ i : Fin (m + 1),
      p.getVert (2 * i.val) = Sum.inl (vertexAt i) := by
    intro i
    exact Classical.choose_spec ((hparity (2 * i.val) (by omega)).1 (by omega))
  let edgeAt : Fin m → E := fun i =>
    Classical.choose ((hparity (2 * i.val + 1) (by omega)).2 (by omega))
  have edgeAt_eq : ∀ i : Fin m,
      p.getVert (2 * i.val + 1) = Sum.inr (edgeAt i) := by
    intro i
    exact Classical.choose_spec ((hparity (2 * i.val + 1) (by omega)).2 (by omega))
  have edgeAt_colored : ∀ i : Fin m, ∃ c, phi (edgeAt i) = some c := by
    intro i
    have ha := p.adj_getVert_succ (i := 2 * i.val) (by rw [hm]; omega)
    rw [vertexAt_eq ⟨i.val, by omega⟩, edgeAt_eq i] at ha
    have hc : phi (edgeAt i) = some alpha ∨ phi (edgeAt i) = some beta := by
      simpa [TwoColorIncidenceGraph] using ha.2
    rcases hc with hc | hc
    · exact ⟨alpha, hc⟩
    · exact ⟨beta, hc⟩
  have edgeAt_colors : ∀ i : Fin m,
      phi (edgeAt i) = some alpha ∨ phi (edgeAt i) = some beta := by
    intro i
    have ha := p.adj_getVert_succ (i := 2 * i.val) (by rw [hm]; omega)
    rw [vertexAt_eq ⟨i.val, by omega⟩, edgeAt_eq i] at ha
    simpa [TwoColorIncidenceGraph] using ha.2
  let reversedVertex : Fin (m + 1) → V := fun i =>
    if hi : i.val = 0 then vertexAt 0
    else vertexAt ⟨m + 1 - i.val, by omega⟩
  let reversedEdge : Fin m → E := fun i =>
    if hi : i.val = 0 then e0
    else edgeAt ⟨m - i.val, by omega⟩
  have hvzero : reversedVertex ⟨0, by omega⟩ =
      T.vertex ⟨0, Nat.zero_lt_succ T.length⟩ := by
    simp only [reversedVertex, dif_pos rfl]
    have hh := vertexAt_eq (0 : Fin (m + 1))
    exact Sum.inl.inj (hh.symm.trans (by simpa using p.getVert_zero))
  have hvone : reversedVertex ⟨1, by omega⟩ =
      T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩ := by
    simp only [reversedVertex, dif_neg (by omega)]
    have he : p.getVert p.length =
        Sum.inl (T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩) := by
      simpa using p.getVert_length
    rw [hm] at he
    have hh := vertexAt_eq ⟨m, by omega⟩
    rw [he] at hh
    exact Sum.inl.inj hh.symm
  have vertexAt_injective : Function.Injective vertexAt := by
    intro i j hij
    have hi := vertexAt_eq i
    have hj := vertexAt_eq j
    have heq : p.getVert (2 * i.val) = p.getVert (2 * j.val) := by
      rw [hi, hj, hij]
    have hi' : 2 * i.val ≤ p.length := by rw [hm]; omega
    have hj' : 2 * j.val ≤ p.length := by rw [hm]; omega
    have hinj := hp.getVert_injOn hi' hj' heq
    omega
  have edgeAt_injective : Function.Injective edgeAt := by
    intro i j hij
    have hi := edgeAt_eq i
    have hj := edgeAt_eq j
    have heq : p.getVert (2 * i.val + 1) = p.getVert (2 * j.val + 1) := by
      rw [hi, hj, hij]
    have hi' : 2 * i.val + 1 ≤ p.length := by rw [hm]; omega
    have hj' : 2 * j.val + 1 ≤ p.length := by rw [hm]; omega
    have hinj := hp.getVert_injOn hi' hj' heq
    omega
  have reversedVertex_injective : Function.Injective reversedVertex := by
    intro i j hij
    have hiLt := i.isLt
    have hjLt := j.isLt
    by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
    · apply Fin.ext
      omega
    · simp only [reversedVertex, dif_pos hi, dif_neg hj] at hij
      have hidx := vertexAt_injective hij
      have hidx' := congrArg Fin.val hidx
      apply Fin.ext
      change 0 = m + 1 - j.val at hidx'
      omega
    · simp only [reversedVertex, dif_neg hi, dif_pos hj] at hij
      have hidx := vertexAt_injective hij
      have hidx' := congrArg Fin.val hidx
      apply Fin.ext
      change m + 1 - i.val = 0 at hidx'
      omega
    · simp only [reversedVertex, dif_neg hi, dif_neg hj] at hij
      have hidx := vertexAt_injective hij
      have hidx' := congrArg Fin.val hidx
      apply Fin.ext
      change m + 1 - i.val = m + 1 - j.val at hidx'
      omega
  have reversedEdge_injective : Function.Injective reversedEdge := by
    intro i j hij
    have hiLt := i.isLt
    have hjLt := j.isLt
    by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
    · apply Fin.ext
      omega
    · simp only [reversedEdge, dif_pos hi, dif_neg hj] at hij
      exfalso
      have he0 := htriple.2.2.2.2.1
      obtain ⟨c, hc⟩ := edgeAt_colored ⟨m - j.val, by omega⟩
      rw [← hij] at hc
      rw [he0] at hc
      cases hc
    · simp only [reversedEdge, dif_neg hi, dif_pos hj] at hij
      exfalso
      have he0 := htriple.2.2.2.2.1
      obtain ⟨c, hc⟩ := edgeAt_colored ⟨m - i.val, by omega⟩
      rw [hij] at hc
      rw [he0] at hc
      cases hc
    · simp only [reversedEdge, dif_neg hi, dif_neg hj] at hij
      have hidx := edgeAt_injective hij
      have hidx' := congrArg Fin.val hidx
      apply Fin.ext
      change m - i.val = m - j.val at hidx'
      omega
  have edge_ends : ∀ i : Fin m,
      G.ends (edgeAt i) = s(vertexAt ⟨i.val, by omega⟩, vertexAt i.succ) := by
    intro i
    have hleft := p.adj_getVert_succ (i := 2 * i.val) (by rw [hm]; omega)
    have hright := p.adj_getVert_succ (i := 2 * i.val + 1) (by rw [hm]; omega)
    rw [vertexAt_eq ⟨i.val, by omega⟩, edgeAt_eq i] at hleft
    rw [edgeAt_eq i] at hright
    have hstep : 2 * i.val + 1 + 1 = 2 * i.succ.val := by
      simp [Fin.succ]
      omega
    rw [hstep, vertexAt_eq i.succ] at hright
    have hleft' : Incident G (vertexAt ⟨i.val, by omega⟩) (edgeAt i) := by
      simpa [TwoColorIncidenceGraph] using hleft.1
    have hright' : Incident G (vertexAt i.succ) (edgeAt i) := by
      simpa [TwoColorIncidenceGraph] using hright.1
    have hne : vertexAt ⟨i.val, by omega⟩ ≠ vertexAt i.succ := by
      intro he
      have hi := vertexAt_injective he
      have hv := congrArg Fin.val hi
      have hv' : i.val = i.val + 1 := by simpa [Fin.succ] using hv
      omega
    exact (Sym2.mem_and_mem_iff hne).mp ⟨hleft', hright'⟩
  let U : TreeSequence G e0 :=
    { length := m
      positive := by omega
      vertex := reversedVertex
      edge := reversedEdge
      vertex_injective := reversedVertex_injective
      edge_injective := reversedEdge_injective
      first_edge := by simp [reversedEdge]
      attaches := by
        intro j
        by_cases hj : j.val = 0
        · refine ⟨0, ?_⟩
          obtain ⟨i, hi⟩ := T.attaches ⟨0, T.positive⟩
          have iLt := i.isLt
          have hi0 : i.val = 0 := Nat.eq_zero_of_le_zero
            (Nat.le_of_lt_succ (by simpa using i.isLt))
          have hiV : (i.castLT (Nat.lt_trans i.isLt (Nat.succ_lt_succ (show 0 < T.length by omega)))) =
              (⟨0, by omega⟩ : Fin (T.length + 1)) := by
            apply Fin.ext
            simpa [hi0]
          have heq : T.edge ⟨0, T.positive⟩ = e0 := T.first_edge
          rw [hiV] at hi
          rw [heq] at hi
          have hj0 : j = (⟨0, by omega⟩ : Fin m) := Fin.ext (by simpa using hj)
          have hsucc : (⟨0, by omega⟩ : Fin m).succ = (⟨1, by omega⟩ : Fin (m + 1)) := by
            apply Fin.ext
            rfl
          rw [hj0, hsucc, hvone]
          simp only [reversedVertex, dif_pos rfl]
          have hv0 := hvzero
          simp only [reversedVertex, dif_pos rfl] at hv0
          rw [hv0]
          simp [reversedEdge]
          simpa using hi
        · refine ⟨⟨j.val, by omega⟩, ?_⟩
          let r : Fin m := ⟨m - j.val, by omega⟩
          have he := edge_ends r
          simp [reversedEdge, hj, reversedVertex]
          have hfirst : vertexAt (⟨r.val, by omega⟩ : Fin (m + 1)) =
              vertexAt (⟨m - j.val, by omega⟩ : Fin (m + 1)) := by
            rfl
          have hsecond : vertexAt r.succ =
              vertexAt (⟨m + 1 - j.val, by omega⟩ : Fin (m + 1)) := by
            apply congrArg vertexAt
            apply Fin.ext
            dsimp [r]
            omega
          rw [hfirst, hsecond] at he
          simpa [Fin.succ] using he }
  have tash : TashkinovTree G e0 phi U := by
    intro j hj
    have j0 : j.val ≠ 0 := by omega
    rw [show U.edge j = edgeAt ⟨m - j.val, by omega⟩ by simp [U, reversedEdge, dif_neg j0]]
    have hc := edgeAt_colors ⟨m - j.val, by omega⟩
    rcases hc with hc | hc
    · refine ⟨0, alpha, hc, ?_⟩
      have hv0 := hvzero
      simp only [reversedVertex, dif_pos rfl] at hv0
      simp only [U, reversedVertex]
      split
      · simpa [hv0] using halpha
      · rename_i h
        exfalso
        exact h rfl
    · refine ⟨1, beta, hc, ?_⟩
      have hv1 := hvone
      simp [reversedVertex] at hv1
      simp only [U, reversedVertex]
      split
      · rename_i h
        exfalso
        norm_num at h
        omega
      · have hmod : 1 % (j.val + 1) = 1 := by
          apply Nat.mod_eq_of_lt
          omega
        simpa [hv1, hmod] using hbeta
  refine ⟨{
    tree := U
    closingEdge := edgeAt ⟨0, by omega⟩
    length_lower := hmpos
    length_eq := by simp [U, m]
    tashkinov := tash
    first_vertex := by simpa [U] using hvzero
    second_vertex := by simpa [U] using hvone
    closing_ends := by
      have he := edge_ends ⟨0, by omega⟩
      have he' : G.ends (edgeAt ⟨0, by omega⟩) =
          s(vertexAt ⟨1, by omega⟩, vertexAt ⟨0, by omega⟩) :=
        he.trans Sym2.eq_swap
      have hm0 : m ≠ 0 := by omega
      simpa [U, reversedVertex, hm0] using he'
    path_vertices := by
      set_option maxRecDepth 100000 in
        simp only [SimpleGraph.Walk.mem_support_iff_exists_getVert]
      change ∀ v, (∃ n, p.getVert n = Sum.inl v ∧ n ≤ p.length) ↔
        ∃ i : Fin (m + 1), v = U.vertex i
      intro v
      constructor
      · rintro ⟨n, hn, hnle⟩
        have hcases : n % 2 = 0 ∨ n % 2 = 1 := by omega
        rcases hcases with heven | hodd
        · let i : Fin (m + 1) := ⟨n / 2, by omega⟩
          have hni : 2 * i.val = n := by
            dsimp [i]
            omega
          have hv : v = vertexAt i := by
            have hh := vertexAt_eq i
            rw [hni] at hh
            exact Sum.inl.inj (hn.symm.trans hh)
          by_cases hi : i.val = 0
          · refine ⟨0, ?_⟩
            have hi' : i = 0 := Fin.ext hi
            rw [hi'] at hv
            simpa [U, reversedVertex] using hv
          · refine ⟨⟨m + 1 - i.val, by change m + 1 - i.val < m + 1; omega⟩, ?_⟩
            let r : Fin (m + 1) := ⟨m + 1 - i.val, by omega⟩
            have hr : reversedVertex r = vertexAt i := by
              have hil := i.isLt
              dsimp [reversedVertex, r]
              rw [dif_neg (by omega)]
              apply congrArg vertexAt
              apply Fin.ext
              change m + 1 - (m + 1 - i.val) = i.val
              omega
            exact hv.trans (by simpa [U] using hr.symm)
        · have hh := (hparity n hnle).2 hodd
          rw [hn] at hh
          rcases hh with ⟨e, he⟩
          cases he
      · rintro ⟨i, rfl⟩
        by_cases hi : i.val = 0
        · refine ⟨0, ?_, by omega⟩
          have hi' : i = 0 := Fin.ext hi
          subst i
          simpa [U, reversedVertex] using vertexAt_eq (0 : Fin (m + 1))
        · let q : Fin (m + 1) := ⟨m + 1 - i.val, by omega⟩
          refine ⟨2 * q.val, ?_, ?_⟩
          · have hq := vertexAt_eq q
            have hq' : p.getVert (2 * q.val) = Sum.inl (U.vertex i) := by
              have hi0 : ¬ i = 0 := by
                intro h
                apply hi
                simpa [h]
              have hr : reversedVertex i = vertexAt q := by
                dsimp [reversedVertex]
                rw [dif_neg (by simpa using hi)]
              simpa [U] using hq.trans (congrArg Sum.inl hr.symm)
            exact hq'
          · rw [hm]
            dsimp [q]
            omega
    path_edges := by
      set_option maxRecDepth 100000 in
        simp only [SimpleGraph.Walk.mem_support_iff_exists_getVert]
      change ∀ f, (∃ n, p.getVert n = Sum.inr f ∧ n ≤ p.length) ↔
        f = edgeAt ⟨0, by omega⟩ ∨ ∃ j : Fin m, 1 ≤ j.val ∧ f = U.edge j
      intro f
      constructor
      · rintro ⟨n, hn, hnle⟩
        have hcases : n % 2 = 0 ∨ n % 2 = 1 := by omega
        rcases hcases with heven | hodd
        · have hh := (hparity n hnle).1 heven
          rw [hn] at hh
          rcases hh with ⟨v, hv⟩
          cases hv
        · let q : Fin m := ⟨n / 2, by omega⟩
          have hnq : 2 * q.val + 1 = n := by
            dsimp [q]
            omega
          have hf : f = edgeAt q := by
            have hh := edgeAt_eq q
            rw [hnq] at hh
            exact Sum.inr.inj (hn.symm.trans hh)
          by_cases hq : q.val = 0
          · left
            have hq' : q = (⟨0, by omega⟩ : Fin m) := by
              apply Fin.ext
              exact hq
            simpa [hq'] using hf
          · right
            have hqpos : 0 < q.val := by omega
            have hmpos' : 0 < m := by omega
            have qlt := q.isLt
            refine ⟨⟨m - q.val, by
              exact Nat.sub_lt hmpos' hqpos⟩, ?_, ?_⟩
            · exact Nat.succ_le_of_lt (Nat.sub_pos_of_lt qlt)
            have hr : reversedEdge ⟨m - q.val, by omega⟩ = edgeAt q := by
              dsimp [reversedEdge]
              rw [dif_neg (by omega)]
              apply congrArg edgeAt
              apply Fin.ext
              dsimp [q]
              have qlt := q.isLt
              omega
            exact hf.trans (by simpa [U] using hr.symm)
      · rintro (hf | ⟨j, hj, hf⟩)
        · subst f
          refine ⟨1, ?_, by rw [hm]; omega⟩
          exact edgeAt_eq ⟨0, by omega⟩
        · let q : Fin m := ⟨m - j.val, by omega⟩
          refine ⟨2 * q.val + 1, ?_, ?_⟩
          · subst f
            have hq := edgeAt_eq q
            have hj0 : ¬ j.val = 0 := by
              intro h
              omega
            have hr : reversedEdge j = edgeAt q := by
              dsimp [reversedEdge]
              rw [dif_neg hj0]
            have hq' : p.getVert (2 * q.val + 1) = Sum.inr (U.edge j) := by
              simpa [U] using hq.trans (congrArg Sum.inr hr.symm)
            exact hq'
          · rw [hm]
            dsimp [q]
            have jlt := j.isLt
            omega
    trunk_edge_ends := by
      change ∀ j : Fin m, 1 ≤ j.val →
        G.ends (U.edge j) = s(U.vertex ⟨j.val, by change j.val < m + 1; omega⟩, U.vertex j.succ)
      intro j hj
      have j0 : j.val ≠ 0 := by omega
      rw [show U.edge j = edgeAt ⟨m - j.val, by omega⟩ by
        simp [U, reversedEdge, j0]]
      have he := edge_ends ⟨m - j.val, by omega⟩
      have he' := he.trans Sym2.eq_swap
      have hv1 : vertexAt (⟨m - j.val, by omega⟩ : Fin m).succ =
          vertexAt ⟨m + 1 - j.val, by omega⟩ := by
        apply congrArg vertexAt
        apply Fin.ext
        simp [Fin.succ]
        omega
      rw [hv1] at he'
      simpa [U, reversedVertex, j0] using he'
  }⟩
