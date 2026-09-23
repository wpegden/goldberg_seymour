import Tablet.BalancedGlobalMaximumTriple
import Tablet.GlobalMaximumTriple
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.MissingColors
import Tablet.NormalCycleEdge
import Tablet.NormalGlobalMaximumTriple
import Tablet.ScheideTrunkRotationColoring
import Tablet.ScheideTrunkRotationCycle
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: ScheideTrunkRotationTree]
theorem ScheideTrunkRotationTree {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi psi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hbalanced : BalancedGlobalMaximumTriple N)
    (j : Fin N.height) (hj : 1 ≤ j.val) (A B : Fin k)
    (hAB : A ≠ B)
    (hA : A = (if Odd j.val then N.beta else N.alpha))
    (hB : B = (if Odd j.val then N.alpha else N.beta))
    (hproper : IsProperEdgeColoring G psi)
    (hone : IsOneEdgeUncolored psi (NormalCycleEdge N j))
    (hmissA : A ∈ MissingColors G psi
      (T.vertex (Fin.castLE N.height_upper j)))
    (hmissB : B ∈ MissingColors G psi
      (T.vertex (Fin.castLE N.height_upper
        ⟨(j.val + 1) % N.height, by
          exact Nat.mod_lt _ (by
            have hp := N.height_lower
            omega)⟩)))
    (hshift : ∀ i : Fin j.val,
      psi (NormalCycleEdge N
          (Fin.castLE (Nat.le_of_lt j.isLt) i)) =
        phi (NormalCycleEdge N
          ⟨i.val + 1, by
            have hi := i.isLt
            have hjlt := j.isLt
            omega⟩))
    (hfixed : ∀ f : E,
      (∀ i : Fin (j.val + 1),
        f ≠ NormalCycleEdge N
          (Fin.castLE (Nat.succ_le_iff.mpr j.isLt) i)) →
      psi f = phi f) :
    ∃ T' : TreeSequence G (NormalCycleEdge N j),
      GlobalMaximumTriple G k (NormalCycleEdge N j) psi T' ∧
      T'.length = T.length ∧
      TreeSequenceVertexSet T' = TreeSequenceVertexSet T ∧
      (∀ r : Fin (T'.length + 1), r.val < N.height →
        ∃ i : Fin N.height,
          i.val = (j.val + r.val) % N.height ∧
            T'.vertex r = T.vertex (Fin.castLE N.height_upper i)) ∧
      (∀ r : Fin (T'.length + 1), N.height ≤ r.val →
        ∃ s : Fin (T.length + 1),
          s.val = r.val ∧ T'.vertex r = T.vertex s) ∧
      (∀ r : Fin T'.length, r.val + 1 < N.height →
        ∃ i : Fin N.height,
          i.val = (j.val + r.val) % N.height ∧
            T'.edge r = NormalCycleEdge N i) ∧
      ∀ r : Fin T'.length, N.height - 1 ≤ r.val →
        ∃ s : Fin T.length,
          s.val = r.val ∧ T'.edge r = T.edge s := by
-- BODY
  classical
  obtain ⟨hp3, _hpodd, hcycle_injective, hcycle_ends, hcycle_colors⟩ :=
    ScheideTrunkRotationCycle G k e0 phi T N hbalanced
  let rho : Fin N.height → Fin N.height := fun r => j + r
  have hrho_val (r : Fin N.height) :
      (rho r).val = (j.val + r.val) % N.height := by
    rfl
  have hrho_injective : Function.Injective rho := by
    intro a b hab
    have hmod (r : Fin N.height) :
        (j.val + r.val) % N.height =
          if j.val + r.val < N.height then
            j.val + r.val
          else
            j.val + r.val - N.height := by
      by_cases hr : j.val + r.val < N.height
      · simp [hr, Nat.mod_eq_of_lt hr]
      · rw [if_neg hr, Nat.mod_eq_sub_mod (by omega)]
        rw [Nat.mod_eq_of_lt]
        omega
    have hv := congrArg Fin.val hab
    change (j.val + a.val) % N.height =
      (j.val + b.val) % N.height at hv
    rw [hmod a, hmod b] at hv
    by_cases ha : j.val + a.val < N.height <;>
      by_cases hb : j.val + b.val < N.height <;>
      simp [ha, hb] at hv <;>
      apply Fin.ext <;> omega
  have hrho_surjective : Function.Surjective rho :=
    Finite.injective_iff_surjective.mp hrho_injective
  have hrho_zero : rho ⟨0, by omega⟩ = j := by
    apply Fin.ext
    change (j.val + 0) % N.height = j.val
    simpa using Nat.mod_eq_of_lt j.isLt
  have hrho_succ (r : Fin N.height) (hr : r.val + 1 < N.height) :
      rho ⟨r.val + 1, hr⟩ =
        ⟨((rho r).val + 1) % N.height, Nat.mod_lt _ (by omega)⟩ := by
    apply Fin.ext
    change (j.val + (r.val + 1)) % N.height =
      (((j.val + r.val) % N.height) + 1) % N.height
    calc
      (j.val + (r.val + 1)) % N.height =
          ((j.val + r.val) + 1) % N.height := by congr 1 <;> omega
      _ = (((j.val + r.val) % N.height) + (1 % N.height)) %
          N.height := Nat.add_mod (j.val + r.val) 1 N.height
      _ = (((j.val + r.val) % N.height) + 1) % N.height := by
        rw [Nat.mod_eq_of_lt (by omega : 1 < N.height)]
  let newVertex : Fin (T.length + 1) → V := fun r =>
    if hr : r.val < N.height then
      T.vertex (Fin.castLE N.height_upper (rho ⟨r.val, hr⟩))
    else
      T.vertex r
  let newEdge : Fin T.length → E := fun r =>
    if hr : r.val + 1 < N.height then
      NormalCycleEdge N (rho ⟨r.val, by omega⟩)
    else
      T.edge r
  have hvertex_prefix (r : Fin (T.length + 1)) (hr : r.val < N.height) :
      newVertex r =
        T.vertex (Fin.castLE N.height_upper (rho ⟨r.val, hr⟩)) := by
    simp [newVertex, hr]
  have hvertex_tail (r : Fin (T.length + 1)) (hr : N.height ≤ r.val) :
      newVertex r = T.vertex r := by
    simp [newVertex, show ¬ r.val < N.height by omega]
  have hedge_prefix (r : Fin T.length) (hr : r.val + 1 < N.height) :
      newEdge r = NormalCycleEdge N (rho ⟨r.val, by omega⟩) := by
    simp [newEdge, hr]
  have hedge_tail (r : Fin T.length) (hr : N.height - 1 ≤ r.val) :
      newEdge r = T.edge r := by
    have hnot : ¬ r.val + 1 < N.height := by omega
    simp [newEdge, hnot]
  have hvertex_injective : Function.Injective newVertex := by
    intro a b hab
    by_cases ha : a.val < N.height
    · by_cases hb : b.val < N.height
      · rw [hvertex_prefix a ha, hvertex_prefix b hb] at hab
        have hc := T.vertex_injective hab
        have hr := hrho_injective (Fin.castLE_injective N.height_upper hc)
        apply Fin.ext
        have hv := congrArg (fun q : Fin N.height => q.val) hr
        simpa using hv
      · rw [hvertex_prefix a ha,
          hvertex_tail b (by omega)] at hab
        have hc := congrArg Fin.val (T.vertex_injective hab)
        have hlt := (rho ⟨a.val, ha⟩).isLt
        simp at hc
        omega
    · by_cases hb : b.val < N.height
      · rw [hvertex_tail a (by omega),
          hvertex_prefix b hb] at hab
        have hc := congrArg Fin.val (T.vertex_injective hab)
        have hlt := (rho ⟨b.val, hb⟩).isLt
        simp at hc
        omega
      · rw [hvertex_tail a (by omega),
          hvertex_tail b (by omega)] at hab
        exact T.vertex_injective hab
  have hcycle_tail_ne (i : Fin N.height) (r : Fin T.length)
      (hr : N.height - 1 ≤ r.val) :
      NormalCycleEdge N i ≠ T.edge r := by
    intro heq
    obtain ⟨a, ha⟩ := T.attaches r
    have hpairs := congrArg (fun e => G.ends e) heq
    rw [hcycle_ends i, ha] at hpairs
    rcases Sym2.eq_iff.mp hpairs with hd | hs
    · have hv := congrArg Fin.val (T.vertex_injective hd.1)
      have hi := i.isLt
      simp at hv
      omega
    · have hv := congrArg Fin.val (T.vertex_injective hs.2)
      have hn := Nat.mod_lt (i.val + 1) (by omega : 0 < N.height)
      simp at hv
      omega
  have hedge_injective : Function.Injective newEdge := by
    intro a b hab
    by_cases ha : a.val + 1 < N.height
    · by_cases hb : b.val + 1 < N.height
      · rw [hedge_prefix a ha, hedge_prefix b hb] at hab
        have hc := hcycle_injective hab
        have hr := hrho_injective hc
        apply Fin.ext
        have hv := congrArg (fun q : Fin N.height => q.val) hr
        simpa using hv
      · rw [hedge_prefix a ha, hedge_tail b (by omega)] at hab
        exfalso
        exact (hcycle_tail_ne _ b (by omega)) hab
    · by_cases hb : b.val + 1 < N.height
      · rw [hedge_tail a (by omega), hedge_prefix b hb] at hab
        exfalso
        exact (hcycle_tail_ne _ a (by omega)) hab.symm
      · rw [hedge_tail a (by omega), hedge_tail b (by omega)] at hab
        exact T.edge_injective hab
  have hfirst_edge : newEdge ⟨0, T.positive⟩ = NormalCycleEdge N j := by
    rw [hedge_prefix _ (by
      show 0 + 1 < N.height
      omega)]
    exact congrArg (NormalCycleEdge N) hrho_zero
  have htransport_index (r : Fin T.length)
      (hr : N.height - 1 ≤ r.val) (a : Fin (r.val + 1)) :
      ∃ b : Fin (r.val + 1),
        newVertex (Fin.castLT b
          (Nat.lt_trans b.isLt (Nat.succ_lt_succ r.isLt))) =
          T.vertex (Fin.castLT a
            (Nat.lt_trans a.isLt (Nat.succ_lt_succ r.isLt))) := by
    by_cases ha : a.val < N.height
    · obtain ⟨q, hq⟩ := hrho_surjective ⟨a.val, ha⟩
      let b : Fin (r.val + 1) := ⟨q.val, by
        have hq_lt := q.isLt
        omega⟩
      refine ⟨b, ?_⟩
      rw [hvertex_prefix _ (by simpa [b] using q.isLt)]
      apply congrArg T.vertex
      apply Fin.ext
      have hv := congrArg Fin.val hq
      simpa [b] using hv
    · let b : Fin (r.val + 1) := ⟨a.val, a.isLt⟩
      refine ⟨b, ?_⟩
      rw [hvertex_tail _ (by simpa [b] using (show N.height ≤ a.val by omega))]
  have hattaches : ∀ r : Fin T.length, ∃ a : Fin (r.val + 1),
      G.ends (newEdge r) =
        s(newVertex r.succ,
          newVertex (Fin.castLT a
            (Nat.lt_trans a.isLt (Nat.succ_lt_succ r.isLt)))) := by
    intro r
    by_cases hr : r.val + 1 < N.height
    · let a : Fin (r.val + 1) := ⟨r.val, Nat.lt_succ_self _⟩
      refine ⟨a, ?_⟩
      rw [hedge_prefix r hr, hcycle_ends,
        hvertex_prefix r.succ (by simpa using hr),
        hvertex_prefix (Fin.castLT a
          (Nat.lt_trans a.isLt (Nat.succ_lt_succ r.isLt))) (by
            simp [a]
            omega)]
      apply Sym2.eq_iff.mpr
      right
      constructor
      · apply congrArg T.vertex
        apply Fin.ext
        rfl
      · apply congrArg T.vertex
        apply Fin.ext
        have hs := hrho_succ ⟨r.val, by omega⟩ hr
        have hv := congrArg (fun q : Fin N.height => q.val) hs.symm
        simpa using hv
    · obtain ⟨a, ha⟩ := T.attaches r
      obtain ⟨b, hb⟩ := htransport_index r (by omega) a
      refine ⟨b, ?_⟩
      rw [hedge_tail r (by omega), ha,
        hvertex_tail r.succ (by simp; omega), hb]
  let T' : TreeSequence G (NormalCycleEdge N j) :=
    { length := T.length
      positive := T.positive
      vertex := newVertex
      edge := newEdge
      vertex_injective := hvertex_injective
      edge_injective := hedge_injective
      first_edge := hfirst_edge
      attaches := hattaches }
  have hnew_zero :
      T'.vertex ⟨0, Nat.zero_lt_succ T'.length⟩ =
        T.vertex (Fin.castLE N.height_upper j) := by
    change newVertex ⟨0, Nat.zero_lt_succ T.length⟩ = _
    rw [hvertex_prefix _ (by
      show 0 < N.height
      omega)]
    exact congrArg (fun q => T.vertex (Fin.castLE N.height_upper q)) hrho_zero
  have hnew_one :
      T'.vertex ⟨1, Nat.succ_lt_succ T'.positive⟩ =
        T.vertex (Fin.castLE N.height_upper
          ⟨(j.val + 1) % N.height, Nat.mod_lt _ (by omega)⟩) := by
    change newVertex ⟨1, Nat.succ_lt_succ T.positive⟩ = _
    rw [hvertex_prefix _ (by
      show 1 < N.height
      omega)]
    apply congrArg T.vertex
    apply Fin.ext
    exact hrho_val ⟨1, by omega⟩
  have hpair_colors :
      ({N.alpha, N.beta} : Finset (Fin k)) = {A, B} := by
    by_cases ho : Odd j.val
    · simp [hA, hB, ho, Finset.pair_comm]
    · simp [hA, hB, ho]
  have hcycle_color_pair (q : Fin N.height) (hq : 1 ≤ q.val) :
      phi (NormalCycleEdge N q) = some A ∨
        phi (NormalCycleEdge N q) = some B := by
    have hc := hcycle_colors q hq
    have halpha : N.alpha = A ∨ N.alpha = B := by
      have hm : N.alpha ∈ ({N.alpha, N.beta} : Finset (Fin k)) := by simp
      rw [hpair_colors] at hm
      simpa using hm
    have hbeta : N.beta = A ∨ N.beta = B := by
      have hm : N.beta ∈ ({N.alpha, N.beta} : Finset (Fin k)) := by simp
      rw [hpair_colors] at hm
      simpa using hm
    by_cases ho : Odd q.val
    · rw [if_pos ho] at hc
      rcases halpha with ha | ha
      · left
        simpa [ha] using hc
      · right
        simpa [ha] using hc
    · rw [if_neg ho] at hc
      rcases hbeta with hb | hb
      · left
        simpa [hb] using hc
      · right
        simpa [hb] using hc
  have htrunk_color (r : Fin T.length) (hrpos : 1 ≤ r.val)
      (hr : r.val + 1 < N.height) :
      psi (newEdge r) = some A ∨ psi (newEdge r) = some B := by
    let q : Fin N.height := rho ⟨r.val, by omega⟩
    rw [hedge_prefix r hr]
    change psi (NormalCycleEdge N q) = some A ∨
      psi (NormalCycleEdge N q) = some B
    have hqj : q ≠ j := by
      intro heq
      have hz := hrho_injective (heq.trans hrho_zero.symm)
      have hv := congrArg Fin.val hz
      simp at hv
      omega
    by_cases hq : q.val < j.val
    · let a : Fin j.val := ⟨q.val, hq⟩
      have hs := hshift a
      have hc := hcycle_color_pair
        ⟨a.val + 1, by
          have hjlt := j.isLt
          simp [a] at *
          omega⟩ (by simp [a])
      have hqa : Fin.castLE (Nat.le_of_lt j.isLt) a = q := by
        apply Fin.ext
        rfl
      rw [hqa] at hs
      rw [hs]
      simpa [a] using hc
    · have hqgt : j.val < q.val := by
        have hn : q.val ≠ j.val := by
          intro hn
          apply hqj
          apply Fin.ext
          exact hn
        omega
      have hf : psi (NormalCycleEdge N q) = phi (NormalCycleEdge N q) := by
        apply hfixed
        intro a heq
        have hi := hcycle_injective heq
        have hv := congrArg Fin.val hi
        simp at hv
        omega
      rw [hf]
      exact hcycle_color_pair q (by omega)
  have hmissing_preserved (v : V) (c : Fin k)
      (hcA : c ≠ A) (hcB : c ≠ B)
      (hc : c ∈ MissingColors G phi v) :
      c ∈ MissingColors G psi v := by
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ,
      true_and] at hc ⊢
    intro hpresent
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
      true_and] at hpresent
    obtain ⟨f, hfv, hfc⟩ := hpresent
    by_cases hspecial : ∃ q : Fin (j.val + 1),
        f = NormalCycleEdge N
          (Fin.castLE (Nat.succ_le_iff.mpr j.isLt) q)
    · obtain ⟨q, hq⟩ := hspecial
      by_cases hlast : q.val = j.val
      · have hqj : Fin.castLE (Nat.succ_le_iff.mpr j.isLt) q = j := by
          apply Fin.ext
          exact hlast
        rw [hq, hqj, hone.1] at hfc
        simp at hfc
      · let a : Fin j.val := ⟨q.val, by omega⟩
        have hqa : Fin.castLE (Nat.le_of_lt j.isLt) a =
            Fin.castLE (Nat.succ_le_iff.mpr j.isLt) q := by
          apply Fin.ext
          rfl
        have hs := hshift a
        rw [hq, ← hqa, hs] at hfc
        have hpair := hcycle_color_pair
          ⟨a.val + 1, by
            have hjlt := j.isLt
            simp [a] at *
            omega⟩ (by simp [a])
        rcases hpair with hpair | hpair
        · rw [hpair] at hfc
          exact hcA (Option.some.inj hfc.symm)
        · rw [hpair] at hfc
          exact hcB (Option.some.inj hfc.symm)
    · have hfix : psi f = phi f := by
        apply hfixed
        intro q heq
        exact hspecial ⟨q, heq⟩
      apply hc
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨f, hfv, hfix.symm.trans hfc⟩
  have htashkinov : TashkinovTree G (NormalCycleEdge N j) psi T' := by
    intro r hrpos
    change ∃ a : Fin (r.val + 1), ∃ c : Fin k,
      psi (newEdge r) = some c ∧
        c ∈ MissingColors G psi
          (newVertex (Fin.castLT a
            (Nat.lt_trans a.isLt (Nat.succ_lt_succ r.isLt))))
    by_cases hr : r.val + 1 < N.height
    · rcases htrunk_color r hrpos hr with hc | hc
      · let a : Fin (r.val + 1) := ⟨0, by omega⟩
        refine ⟨a, A, hc, ?_⟩
        change A ∈ MissingColors G psi
          (newVertex ⟨0, Nat.zero_lt_succ T.length⟩)
        rw [show newVertex ⟨0, Nat.zero_lt_succ T.length⟩ =
            T'.vertex ⟨0, Nat.zero_lt_succ T'.length⟩ by rfl,
          hnew_zero]
        exact hmissA
      · let a : Fin (r.val + 1) := ⟨1, by omega⟩
        refine ⟨a, B, hc, ?_⟩
        change B ∈ MissingColors G psi
          (newVertex ⟨1, Nat.succ_lt_succ T.positive⟩)
        rw [show newVertex ⟨1, Nat.succ_lt_succ T.positive⟩ =
            T'.vertex ⟨1, Nat.succ_lt_succ T'.positive⟩ by rfl,
          hnew_one]
        exact hmissB
    · obtain ⟨a, c, hc, hcmiss⟩ := N.global.2.1 r hrpos
      have htail : N.height - 1 ≤ r.val := by omega
      have hfix : psi (T.edge r) = phi (T.edge r) := by
        apply hfixed
        intro q heq
        exact (hcycle_tail_ne _ r htail) heq.symm
      have hcnew : psi (newEdge r) = some c := by
        rw [hedge_tail r htail, hfix]
        exact hc
      by_cases hcA : c = A
      · let b : Fin (r.val + 1) := ⟨0, by omega⟩
        refine ⟨b, c, hcnew, ?_⟩
        subst c
        change A ∈ MissingColors G psi
          (newVertex ⟨0, Nat.zero_lt_succ T.length⟩)
        rw [show newVertex ⟨0, Nat.zero_lt_succ T.length⟩ =
            T'.vertex ⟨0, Nat.zero_lt_succ T'.length⟩ by rfl,
          hnew_zero]
        exact hmissA
      · by_cases hcB : c = B
        · let b : Fin (r.val + 1) := ⟨1, by omega⟩
          refine ⟨b, c, hcnew, ?_⟩
          subst c
          change B ∈ MissingColors G psi
            (newVertex ⟨1, Nat.succ_lt_succ T.positive⟩)
          rw [show newVertex ⟨1, Nat.succ_lt_succ T.positive⟩ =
              T'.vertex ⟨1, Nat.succ_lt_succ T'.positive⟩ by rfl,
            hnew_one]
          exact hmissB
        · obtain ⟨b, hb⟩ := htransport_index r htail a
          refine ⟨b, c, hcnew, ?_⟩
          rw [hb]
          exact hmissing_preserved _ c hcA hcB hcmiss
  have hvertex_set : TreeSequenceVertexSet T' = TreeSequenceVertexSet T := by
    apply Finset.ext
    intro v
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨a, rfl⟩
      change ∃ b : Fin (T.length + 1), T.vertex b = newVertex a
      by_cases ha : a.val < N.height
      · refine ⟨Fin.castLE N.height_upper (rho ⟨a.val, ha⟩), ?_⟩
        exact (hvertex_prefix a ha).symm
      · refine ⟨a, ?_⟩
        exact (hvertex_tail a (by omega)).symm
    · rintro ⟨a, rfl⟩
      change ∃ b : Fin (T.length + 1), newVertex b = T.vertex a
      by_cases ha : a.val < N.height
      · obtain ⟨q, hq⟩ := hrho_surjective ⟨a.val, ha⟩
        let b : Fin (T.length + 1) :=
          ⟨q.val, Nat.lt_of_lt_of_le q.isLt N.height_upper⟩
        refine ⟨b, ?_⟩
        rw [hvertex_prefix b (by simpa [b] using q.isLt)]
        apply congrArg T.vertex
        apply Fin.ext
        have hv := congrArg Fin.val hq
        simpa [b] using hv
      · refine ⟨a, hvertex_tail a (by omega)⟩
  have hglobal :
      GlobalMaximumTriple G k (NormalCycleEdge N j) psi T' := by
    refine ⟨⟨N.global.1.1, N.global.1.2.1,
      N.global.1.2.2.1, hproper, hone⟩, htashkinov, ?_⟩
    rw [hvertex_set]
    exact N.global.2.2
  refine ⟨T', hglobal, rfl, hvertex_set, ?_, ?_, ?_, ?_⟩
  · intro r hr
    let i : Fin N.height := rho ⟨r.val, hr⟩
    refine ⟨i, ?_, ?_⟩
    · exact hrho_val ⟨r.val, hr⟩
    · change newVertex r = _
      rw [hvertex_prefix r hr]
  · intro r hr
    refine ⟨⟨r.val, by simpa [T'] using r.isLt⟩, rfl, ?_⟩
    change newVertex r = _
    exact hvertex_tail r hr
  · intro r hr
    let i : Fin N.height := rho ⟨r.val, by omega⟩
    refine ⟨i, ?_, ?_⟩
    · exact hrho_val ⟨r.val, by omega⟩
    · change newEdge r = _
      rw [hedge_prefix r hr]
  · intro r hr
    refine ⟨⟨r.val, by simpa [T'] using r.isLt⟩, rfl, ?_⟩
    change newEdge r = _
    exact hedge_tail r hr
