import Tablet.BalancedGlobalMaximumTriple
import Tablet.AdjacentEdges
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MissingColors
import Tablet.NormalCycleEdge
import Tablet.NormalGlobalMaximumTriple
import Tablet.PresentColors
import Tablet.ScheideTrunkRotationCycle
import Tablet.TreeSequence

-- [TABLET NODE: ScheideTrunkRotationColoring]
theorem ScheideTrunkRotationColoring {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hbalanced : BalancedGlobalMaximumTriple N)
    (j : Fin N.height) (hj : 1 ≤ j.val) :
    ∃ (psi : PartialEdgeColoring E k) (A B : Fin k),
      A ≠ B ∧
      A = (if Odd j.val then N.beta else N.alpha) ∧
      B = (if Odd j.val then N.alpha else N.beta) ∧
      IsProperEdgeColoring G psi ∧
      IsOneEdgeUncolored psi (NormalCycleEdge N j) ∧
      A ∈ MissingColors G psi
        (T.vertex (Fin.castLE N.height_upper j)) ∧
      B ∈ MissingColors G psi
        (T.vertex (Fin.castLE N.height_upper
          ⟨(j.val + 1) % N.height, by
            exact Nat.mod_lt _ (by
              have hp := N.height_lower
              omega)⟩)) ∧
      (∀ i : Fin j.val,
        psi (NormalCycleEdge N
            (Fin.castLE (Nat.le_of_lt j.isLt) i)) =
          phi (NormalCycleEdge N
            ⟨i.val + 1, by
              have hi := i.isLt
              have hjlt := j.isLt
              omega⟩)) ∧
      (∀ f : E,
        (∀ i : Fin (j.val + 1),
          f ≠ NormalCycleEdge N
            (Fin.castLE (Nat.succ_le_iff.mpr j.isLt) i)) →
        psi f = phi f) ∧
      ∀ r : Fin T.length, N.height - 1 ≤ r.val →
        psi (T.edge r) = phi (T.edge r) := by
-- BODY
  classical
  obtain ⟨hp3, hpodd, hFinj, hends, hcolors⟩ :=
    ScheideTrunkRotationCycle G k e0 phi T N hbalanced
  let F : Fin N.height → E := NormalCycleEdge N
  let Y : Fin N.height → V := fun i =>
    T.vertex (Fin.castLE N.height_upper i)
  let nxt : Fin N.height → Fin N.height := fun i =>
    ⟨(i.val + 1) % N.height, Nat.mod_lt _ (by omega)⟩
  have hFinj' : Function.Injective F := by
    simpa [F] using hFinj
  have hYinj : Function.Injective Y := by
    intro a b hab
    apply Fin.ext
    have hcast := T.vertex_injective hab
    simpa using congrArg Fin.val hcast
  have hends' (i : Fin N.height) :
      G.ends (F i) = s(Y i, Y (nxt i)) := by
    simpa [F, Y, nxt] using hends i
  have hinc (i : Fin N.height) (v : V) :
      Incident G v (F i) ↔ v = Y i ∨ v = Y (nxt i) := by
    rw [Incident, hends' i]
    simp
  have hnxt_val (i : Fin N.height) (hi : i.val + 1 < N.height) :
      (nxt i).val = i.val + 1 := by
    simp [nxt, Nat.mod_eq_of_lt hi]
  have hadj_succ (i : Fin N.height) (hi : i.val + 1 < N.height) :
      AdjacentEdges G (F i)
        (F ⟨i.val + 1, hi⟩) := by
    refine ⟨Y ⟨i.val + 1, hi⟩, ?_, ?_⟩
    · apply (hinc i _).2
      right
      apply congrArg Y
      apply Fin.ext
      exact (hnxt_val i hi).symm
    · apply (hinc ⟨i.val + 1, hi⟩ _).2
      exact Or.inl rfl
  have hFzero : F ⟨0, by omega⟩ = e0 := by
    simp [F, NormalCycleEdge]
  have hab : N.alpha ≠ N.beta := by
    intro heq
    let one : Fin N.height := ⟨1, by omega⟩
    have hone : phi (F one) = some N.alpha := by
      simpa [F, one] using hcolors one (by simp [one])
    have hi : Incident G (Y one) (F one) := by
      apply (hinc one _).2
      exact Or.inl rfl
    have hpresent : N.beta ∈ PresentColors G phi (Y one) := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨F one, hi, by simpa [heq] using hone⟩
    have hmissing : N.beta ∉ PresentColors G phi (Y one) := by
      simpa [MissingColors, Y, one] using N.beta_missing
    exact hmissing hpresent
  let A : Fin k := if Odd j.val then N.beta else N.alpha
  let B : Fin k := if Odd j.val then N.alpha else N.beta
  have hAB : A ≠ B := by
    by_cases ho : Odd j.val
    · simpa [A, B, ho] using hab.symm
    · simpa [A, B, ho] using hab
  let psi : PartialEdgeColoring E k := fun f =>
    if f = F j then none
    else if h : ∃ i : Fin j.val,
        f = F (Fin.castLE (Nat.le_of_lt j.isLt) i) then
      phi (F ⟨(Classical.choose h).val + 1, by
        have hi := (Classical.choose h).isLt
        omega⟩)
    else phi f
  have hpsi_j : psi (F j) = none := by
    simp [psi]
  have hpsi_shift (i : Fin j.val) :
      psi (F (Fin.castLE (Nat.le_of_lt j.isLt) i)) =
        phi (F ⟨i.val + 1, by omega⟩) := by
    have hne : F (Fin.castLE (Nat.le_of_lt j.isLt) i) ≠ F j := by
      intro he
      have hh := hFinj' he
      have hv := congrArg Fin.val hh
      simp at hv
      omega
    have hex : ∃ t : Fin j.val,
        F (Fin.castLE (Nat.le_of_lt j.isLt) i) =
          F (Fin.castLE (Nat.le_of_lt j.isLt) t) := ⟨i, rfl⟩
    rw [show psi (F (Fin.castLE (Nat.le_of_lt j.isLt) i)) =
        (if F (Fin.castLE (Nat.le_of_lt j.isLt) i) = F j then none
         else if h : ∃ t : Fin j.val,
            F (Fin.castLE (Nat.le_of_lt j.isLt) i) =
              F (Fin.castLE (Nat.le_of_lt j.isLt) t) then
           phi (F ⟨(Classical.choose h).val + 1, by
             have ht := (Classical.choose h).isLt
             omega⟩)
         else phi (F (Fin.castLE (Nat.le_of_lt j.isLt) i))) by rfl]
    rw [if_neg hne, dif_pos hex]
    apply congrArg phi
    apply congrArg F
    apply Fin.ext
    have hspec := Classical.choose_spec hex
    have hind := hFinj' hspec
    simpa using congrArg Fin.val hind.symm
  have hpsi_fixed (f : E)
      (hf : ∀ i : Fin (j.val + 1),
        f ≠ F (Fin.castLE (Nat.succ_le_iff.mpr j.isLt) i)) :
      psi f = phi f := by
    have hfj : f ≠ F j := by
      let q : Fin (j.val + 1) := ⟨j.val, Nat.lt_succ_self _⟩
      simpa [q] using hf q
    have hs : ¬ ∃ i : Fin j.val,
        f = F (Fin.castLE (Nat.le_of_lt j.isLt) i) := by
      rintro ⟨i, hi⟩
      let q : Fin (j.val + 1) := ⟨i.val, by omega⟩
      apply hf q
      refine hi.trans ?_
      apply congrArg F
      apply Fin.ext
      rfl
    simp [psi, hfj, hs]
  have holdProper : IsProperEdgeColoring G phi := N.global.1.2.2.2.1
  have holdOne : IsOneEdgeUncolored phi e0 := N.global.1.2.2.2.2
  have hcolors' (q : Fin N.height) (hq : 1 ≤ q.val) :
      phi (F q) = if Odd q.val then some N.alpha else some N.beta := by
    simpa [F] using hcolors q hq
  let z : Fin N.height := ⟨0, by omega⟩
  let o : Fin N.height := ⟨1, by omega⟩
  have halpha_absent (f : E) (hf : Incident G (Y z) f) :
      phi f ≠ some N.alpha := by
    intro hfc
    have hpresent : N.alpha ∈ PresentColors G phi (Y z) := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨f, hf, hfc⟩
    have hmissing : N.alpha ∉ PresentColors G phi (Y z) := by
      simpa [MissingColors, Y, z] using N.alpha_missing
    exact hmissing hpresent
  have hbeta_absent (f : E) (hf : Incident G (Y o) f) :
      phi f ≠ some N.beta := by
    intro hfc
    have hpresent : N.beta ∈ PresentColors G phi (Y o) := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨f, hf, hfc⟩
    have hmissing : N.beta ∉ PresentColors G phi (Y o) := by
      simpa [MissingColors, Y, o] using N.beta_missing
    exact hmissing hpresent
  have hshift_adj (i t : Fin j.val) (hit : i ≠ t)
      (had : AdjacentEdges G
        (F (Fin.castLE (Nat.le_of_lt j.isLt) i))
        (F (Fin.castLE (Nat.le_of_lt j.isLt) t))) :
      i.val + 1 = t.val ∨ t.val + 1 = i.val := by
    obtain ⟨v, hvi, hvt⟩ := had
    rcases (hinc (Fin.castLE (Nat.le_of_lt j.isLt) i) v).mp hvi with
      hil | hir
    · rcases (hinc (Fin.castLE (Nat.le_of_lt j.isLt) t) v).mp hvt with
        htl | htr
      · have he := hYinj (hil.symm.trans htl)
        have hv := congrArg Fin.val he
        exfalso
        apply hit
        apply Fin.ext
        simpa using hv
      · have he := hYinj (hil.symm.trans htr)
        have hv := congrArg Fin.val he
        rw [hnxt_val _ (by simp; omega)] at hv
        right
        simpa using hv.symm
    · rcases (hinc (Fin.castLE (Nat.le_of_lt j.isLt) t) v).mp hvt with
        htl | htr
      · have he := hYinj (hir.symm.trans htl)
        have hv := congrArg Fin.val he
        rw [hnxt_val _ (by simp; omega)] at hv
        left
        simpa using hv
      · have he := hYinj (hir.symm.trans htr)
        have hv := congrArg Fin.val he
        rw [hnxt_val _ (by simp; omega), hnxt_val _ (by simp; omega)] at hv
        exfalso
        apply hit
        apply Fin.ext
        have hv' : i.val + 1 = t.val + 1 := by simpa using hv
        omega
  have hno_mixed (i : Fin j.val) (f : E)
      (hfj : f ≠ F j)
      (hfs : ¬ ∃ t : Fin j.val,
        f = F (Fin.castLE (Nat.le_of_lt j.isLt) t))
      (had : AdjacentEdges G
        (F (Fin.castLE (Nat.le_of_lt j.isLt) i)) f)
      (c : Fin k)
      (hci : psi (F (Fin.castLE (Nat.le_of_lt j.isLt) i)) = some c) :
      phi f ≠ some c := by
    have hisucc : i.val + 1 < N.height := by
      have hi := i.isLt
      have hjlt := j.isLt
      omega
    let succ : Fin N.height := ⟨i.val + 1, hisucc⟩
    have hcarrier : phi (F succ) = some c := by
      rw [← hpsi_shift i]
      simpa [succ] using hci
    have hf_succ : f ≠ F succ := by
      intro he
      by_cases heq : i.val + 1 = j.val
      · apply hfj
        rw [he]
        apply congrArg F
        apply Fin.ext
        exact heq
      · apply hfs
        let t : Fin j.val := ⟨i.val + 1, by omega⟩
        refine ⟨t, ?_⟩
        rw [he]
        apply congrArg F
        apply Fin.ext
        rfl
    obtain ⟨v, hvi, hvf⟩ := had
    rcases (hinc (Fin.castLE (Nat.le_of_lt j.isLt) i) v).mp hvi with
      hleft | hright
    · by_cases hi0 : i.val = 0
      · have hcol : c = N.alpha := by
          have hc := hcolors' succ (by simp [succ])
          rw [if_pos (by simpa [succ, hi0] : Odd succ.val)] at hc
          rw [hcarrier] at hc
          simpa using hc
        intro hfc
        apply halpha_absent f
        · rw [hleft] at hvf
          have hindex : Fin.castLE (Nat.le_of_lt j.isLt) i = z := by
            apply Fin.ext
            simp [z, hi0]
          rwa [hindex] at hvf
        simpa [hcol] using hfc
      · by_cases hi1 : i.val = 1
        · have hcol : c = N.beta := by
            have hc := hcolors' succ (by simp [succ])
            rw [if_neg (by simp [succ, hi1] : ¬ Odd succ.val)] at hc
            rw [hcarrier] at hc
            simpa using hc
          intro hfc
          apply hbeta_absent f
          · rw [hleft] at hvf
            have hindex : Fin.castLE (Nat.le_of_lt j.isLt) i = o := by
              apply Fin.ext
              simp [o, hi1]
            rwa [hindex] at hvf
          simpa [hcol] using hfc
        · let prev : Fin N.height := ⟨i.val - 1, by omega⟩
          have hprev_color : phi (F prev) = some c := by
            have hp := hcolors' prev (by simp [prev]; omega)
            have hs := hcolors' succ (by simp [succ])
            have hodd : Odd (i.val - 1) ↔ Odd (i.val + 1) := by
              have heq : i.val + 1 = (i.val - 1) + 2 := by omega
              rw [Nat.odd_iff, Nat.odd_iff]
              omega
            rw [hcarrier] at hs
            by_cases ho : Odd (i.val - 1)
            · rw [if_pos ho] at hp
              rw [if_pos (hodd.mp ho)] at hs
              simpa using hp.trans hs.symm
            · rw [if_neg ho] at hp
              rw [if_neg (mt hodd.mpr ho)] at hs
              simpa using hp.trans hs.symm
          have hf_prev : f ≠ F prev := by
            intro he
            apply hfs
            let t : Fin j.val := ⟨i.val - 1, by omega⟩
            refine ⟨t, ?_⟩
            rw [he]
            apply congrArg F
            apply Fin.ext
            rfl
          have hadprev : AdjacentEdges G (F prev) f := by
            refine ⟨Y (Fin.castLE (Nat.le_of_lt j.isLt) i), ?_, ?_⟩
            · apply (hinc prev _).2
              right
              apply congrArg Y
              apply Fin.ext
              rw [hnxt_val prev (by simp [prev]; omega)]
              simp [prev]
              omega
            · simpa [hleft] using hvf
          exact holdProper hf_prev.symm hadprev hprev_color
    · have hadold : AdjacentEdges G (F succ) f := by
        refine ⟨v, ?_, hvf⟩
        apply (hinc succ v).2
        left
        rw [hright]
        apply congrArg Y
        apply Fin.ext
        rw [hnxt_val _ (by simp; omega)]
        simp [succ]
      exact holdProper hf_succ.symm hadold hcarrier
  have hproperPsi : IsProperEdgeColoring G psi := by
    intro e f c hef had hce
    by_cases hej : e = F j
    · rw [hej, hpsi_j] at hce
      simp at hce
    by_cases hfej : f = F j
    · rw [hfej, hpsi_j]
      simp
    by_cases hes : ∃ i : Fin j.val,
        e = F (Fin.castLE (Nat.le_of_lt j.isLt) i)
    · obtain ⟨i, rfl⟩ := hes
      by_cases hfs : ∃ t : Fin j.val,
          f = F (Fin.castLE (Nat.le_of_lt j.isLt) t)
      · obtain ⟨t, rfl⟩ := hfs
        have hit : i ≠ t := by
          intro he
          subst t
          exact hef rfl
        have hind := hshift_adj i t hit had
        rw [hpsi_shift i] at hce
        rw [hpsi_shift t]
        rcases hind with hit | hti
        · let qi : Fin N.height := ⟨i.val + 1, by omega⟩
          let qt : Fin N.height := ⟨t.val + 1, by omega⟩
          have hqne : F qi ≠ F qt := by
            intro he
            have hh := hFinj' he
            have hv := congrArg Fin.val hh
            simp [qi, qt, hit] at hv
          have hqadj : AdjacentEdges G (F qi) (F qt) := by
            have ha := hadj_succ qi (by simp [qi, qt]; omega)
            simpa [qi, qt, hit] using ha
          exact holdProper hqne hqadj hce
        · let qt : Fin N.height := ⟨t.val + 1, by omega⟩
          let qi : Fin N.height := ⟨i.val + 1, by omega⟩
          have hqne : F qi ≠ F qt := by
            intro he
            have hh := hFinj' he
            have hv := congrArg Fin.val hh
            simp [qi, qt, hti] at hv
          have hqadj : AdjacentEdges G (F qi) (F qt) := by
            have ha := hadj_succ qt (by simp [qt, qi]; omega)
            rcases ha with ⟨v, hv1, hv2⟩
            exact ⟨v, by simpa [qt, qi, hti] using hv2,
              by simpa [qt, qi, hti] using hv1⟩
          exact holdProper hqne hqadj hce
      · rw [show psi f = phi f by simp [psi, hfej, hfs]]
        exact hno_mixed i f hfej hfs had c (by simpa using hce)
    · have hpse : psi e = phi e := by simp [psi, hej, hes]
      by_cases hfs : ∃ t : Fin j.val,
          f = F (Fin.castLE (Nat.le_of_lt j.isLt) t)
      · obtain ⟨t, rfl⟩ := hfs
        intro hcf
        obtain ⟨v, hve, hvt⟩ := had
        have hno := hno_mixed t e hej hes
          ⟨v, hvt, hve⟩ c hcf
        exact hno (by simpa [hpse] using hce)
      · rw [show psi f = phi f by simp [psi, hfej, hfs]]
        exact holdProper hef had (by simpa [hpse] using hce)
  have honePsi : IsOneEdgeUncolored psi (F j) := by
    refine ⟨hpsi_j, ?_⟩
    intro f hfj
    by_cases hfs : ∃ i : Fin j.val,
        f = F (Fin.castLE (Nat.le_of_lt j.isLt) i)
    · obtain ⟨i, rfl⟩ := hfs
      have hisucc : i.val + 1 < N.height := by
        have hi := i.isLt
        have hjlt := j.isLt
        omega
      have hc := hcolors' ⟨i.val + 1, hisucc⟩ (by simp)
      rw [hpsi_shift i]
      by_cases ho : Odd (i.val + 1)
      · exact ⟨N.alpha, by simpa [ho] using hc⟩
      · exact ⟨N.beta, by simpa [ho] using hc⟩
    · have hf0 : f ≠ e0 := by
        intro he
        apply hfs
        let i : Fin j.val := ⟨0, by omega⟩
        refine ⟨i, ?_⟩
        calc
          f = e0 := he
          _ = F ⟨0, by omega⟩ := hFzero.symm
          _ = F (Fin.castLE (Nat.le_of_lt j.isLt) i) := by
            apply congrArg F
            apply Fin.ext
            rfl
      obtain ⟨c, hc⟩ := holdOne.2 f hf0
      exact ⟨c, by simpa [psi, hfj, hfs] using hc⟩
  have hphi_j : phi (F j) = some B := by
    have hc := hcolors' j hj
    by_cases ho : Odd j.val
    · simpa [B, ho] using hc
    · simpa [B, ho] using hc
  have hmissingA : A ∈ MissingColors G psi (Y j) := by
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
      PresentColors, Finset.mem_filter, not_exists, not_and]
    intro f hfinc
    by_cases hfj : f = F j
    · rw [hfj, hpsi_j]
      simp
    by_cases hfs : ∃ t : Fin j.val,
        f = F (Fin.castLE (Nat.le_of_lt j.isLt) t)
    · obtain ⟨t, rfl⟩ := hfs
      have htinc := hfinc
      rcases (hinc (Fin.castLE (Nat.le_of_lt j.isLt) t) (Y j)).mp htinc with
        hleft | hright
      · have he := hYinj hleft
        have hv := congrArg Fin.val he
        simp at hv
        omega
      · have he := hYinj hright
        have hv := congrArg Fin.val he
        rw [hnxt_val _ (by simp; omega)] at hv
        have htj : t.val + 1 = j.val := by simpa using hv.symm
        rw [hpsi_shift t]
        have hindex : (⟨t.val + 1, by omega⟩ : Fin N.height) = j := by
          apply Fin.ext
          exact htj
        rw [hindex, hphi_j]
        intro heq
        exact hAB (Option.some.inj heq).symm
    · have hpsif : psi f = phi f := by simp [psi, hfj, hfs]
      by_cases hj1 : j.val = 1
      · have hA : A = N.beta := by
          have hjodd : Odd j.val := by simpa [hj1]
          simp [A, hjodd]
        rw [hpsif]
        intro hfc
        apply hbeta_absent f
        · have hindex : j = o := by
            apply Fin.ext
            simpa [o] using hj1
          simpa [hindex] using hfinc
        simpa [hA] using hfc
      · have hj2 : 2 ≤ j.val := by omega
        let prev : Fin N.height := ⟨j.val - 1, by omega⟩
        have hprevA : phi (F prev) = some A := by
          have hc := hcolors' prev (by simp [prev]; omega)
          have hpar : Odd (j.val - 1) ↔ ¬ Odd j.val := by
            rw [Nat.odd_iff, Nat.not_odd_iff]
            omega
          by_cases ho : Odd j.val
          · rw [if_neg (fun hp => hpar.mp hp ho)] at hc
            simpa [A, ho] using hc
          · rw [if_pos (hpar.mpr ho)] at hc
            simpa [A, ho] using hc
        have hfprev : f ≠ F prev := by
          intro he
          apply hfs
          let t : Fin j.val := ⟨j.val - 1, by omega⟩
          refine ⟨t, ?_⟩
          rw [he]
          apply congrArg F
          apply Fin.ext
          rfl
        have hprevinc : Incident G (Y j) (F prev) := by
          apply (hinc prev _).2
          right
          apply congrArg Y
          apply Fin.ext
          rw [hnxt_val prev (by simp [prev]; omega)]
          simp [prev]
          omega
        rw [hpsif]
        exact holdProper hfprev.symm ⟨Y j, hprevinc, hfinc⟩ hprevA
  have hmissingB : B ∈ MissingColors G psi (Y (nxt j)) := by
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
      PresentColors, Finset.mem_filter, not_exists, not_and]
    intro f hfinc
    by_cases hfj : f = F j
    · rw [hfj, hpsi_j]
      simp
    by_cases hfs : ∃ t : Fin j.val,
        f = F (Fin.castLE (Nat.le_of_lt j.isLt) t)
    · obtain ⟨t, rfl⟩ := hfs
      rcases (hinc (Fin.castLE (Nat.le_of_lt j.isLt) t) (Y (nxt j))).mp hfinc with
        hleft | hright
      · have he := hYinj hleft
        have hv := congrArg Fin.val he
        by_cases hjlast : j.val + 1 = N.height
        · have ht0 : t.val = 0 := by simpa [nxt, hjlast] using hv.symm
          have hjEven : ¬ Odd j.val := by
            have hpj : Odd (j.val + 1) := by simpa [hjlast] using hpodd
            exact (Nat.odd_add_one.mp hpj)
          have hc := hcolors' ⟨1, by omega⟩ (by simp)
          rw [hpsi_shift t]
          have hindex : (⟨t.val + 1, by omega⟩ : Fin N.height) =
              ⟨1, by omega⟩ := by
            apply Fin.ext
            simp [ht0]
          rw [hindex]
          rw [hc]
          simpa [B, hjEven] using hab
        · rw [hnxt_val j (by omega)] at hv
          simp at hv
          omega
      · have he := hYinj hright
        have htbound : t.val + 1 < N.height := by
          have ht := t.isLt
          have hjlt := j.isLt
          omega
        have hv : (j.val + 1) % N.height = t.val + 1 := by
          have hv' := congrArg Fin.val he
          simpa [nxt, Nat.mod_eq_of_lt htbound] using hv'
        by_cases hjlast : j.val + 1 = N.height
        · simp [hjlast] at hv
        · rw [Nat.mod_eq_of_lt (by omega)] at hv
          omega
    · have hpsif : psi f = phi f := by simp [psi, hfj, hfs]
      have hjinc : Incident G (Y (nxt j)) (F j) := by
        apply (hinc j _).2
        exact Or.inr rfl
      rw [hpsif]
      exact holdProper (Ne.symm hfj) ⟨Y (nxt j), hjinc, hfinc⟩ hphi_j
  have htail (r : Fin T.length) (hr : N.height - 1 ≤ r.val) :
      psi (T.edge r) = phi (T.edge r) := by
    apply hpsi_fixed
    intro i
    intro he
    let q : Fin N.height :=
      Fin.castLE (Nat.succ_le_iff.mpr j.isLt) i
    obtain ⟨a, ha⟩ := T.attaches r
    have hpairs :
        s(T.vertex r.succ,
            T.vertex (Fin.castLT a
              (Nat.lt_trans a.isLt (Nat.succ_lt_succ r.isLt)))) =
          s(Y q, Y (nxt q)) := by
      rw [← ha, he]
      exact hends' q
    rcases Sym2.eq_iff.mp hpairs with hd | hs
    · have hv := T.vertex_injective hd.1
      have hval := congrArg Fin.val hv
      change r.val + 1 = q.val at hval
      have hq : q.val < N.height := q.isLt
      omega
    · have hv := T.vertex_injective hs.1
      have hval := congrArg Fin.val hv
      change r.val + 1 = (Fin.castLE N.height_upper (nxt q)).val at hval
      have hq : (nxt q).val < N.height := (nxt q).isLt
      simp at hval
      omega
  refine ⟨psi, A, B, hAB, rfl, rfl, hproperPsi, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [F] using honePsi
  · simpa [Y] using hmissingA
  · simpa [Y, nxt] using hmissingB
  · intro i
    simpa [F] using hpsi_shift i
  · intro f hf
    apply hpsi_fixed f
    simpa [F] using hf
  · exact htail
