import Tablet.ColoredVertexSetElementary
import Tablet.KTriple
import Tablet.MissingColorIncidenceEndpoint
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.TashTreeBadPair
import Tablet.TashTreeControlledInterchange
import Tablet.TashTreeFourUnusedColors
import Tablet.TashTreeMinimumBadPair
import Tablet.TashTreePathIndex
import Tablet.TashTreeProperPrefixElementary
import Tablet.TashkinovTree
import Tablet.TreeFreeColors
import Tablet.TreeSequence
import Tablet.TreeSequencePrefix
import Tablet.TreeUsedColors
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapMissingBehavior

-- [TABLET NODE: TashTreeLastIndexThirdNormalForm]
theorem TashTreeLastIndexThirdNormalForm {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : 2 < TashTreePathIndex G T)
    (hlast : TashTreePathIndex G T = T.length)
    (gamma : Fin k) (r : Fin T.length) (p : Fin (T.length + 1))
    (hr : r.val + 1 = T.length) (hp : p.val + 1 = T.length)
    (hrgamma : phi (T.edge r) = some gamma)
    (hpgamma : gamma ∈ PresentColors G phi (T.vertex p)) :
    ∃ (phi₃ : PartialEdgeColoring E k) (beta : Fin k)
        (j : Fin (T.length + 1)),
      TashTreeMinimumBadPair G k e0 phi₃ T ∧
        phi₃ (T.edge r) = some gamma ∧
        gamma ∈ PresentColors G phi₃ (T.vertex p) ∧
        j.val + 2 ≤ T.length ∧
        beta ∈ MissingColors G phi₃ (T.vertex j) ∧
        beta ∈ MissingColors G phi₃ (T.vertex (Fin.last T.length)) := by
-- BODY
  classical
  have hlen : 3 ≤ T.length := by omega
  have hlastval : r.val = T.length - 1 := by omega
  have hpval : p.val = T.length - 1 := by omega
  have hbad := hmin.1
  have hproper := hbad.1.2.2.2.1
  have hnot := hbad.2.2
  let P : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - 1) (by omega) (by omega)
  have hP_length : P.length = T.length - 1 := by rfl
  have hPprefix : TreeSequenceInitialSegment P T := by
    refine ⟨by rw [hP_length]; omega, ?_, ?_⟩
    · intro i
      rfl
    · intro i
      rfl
  have hPelementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet P) := by
    apply TashTreeProperPrefixElementary G k e0 phi T P hmin hPprefix
    change T.length - 1 < T.length
    omega
  have hlastmem : T.vertex (Fin.last T.length) ∈
      TreeSequenceVertexSet T := by
    simp [TreeSequenceVertexSet]
  have hprefixmem (i : Fin (T.length + 1)) :
      T.vertex i ∈ TreeSequenceVertexSet T := by
    simp [TreeSequenceVertexSet]
  have hcommon : ∃ u : V, u ∈ TreeSequenceVertexSet T ∧
      ∃ v : V, v ∈ TreeSequenceVertexSet T ∧ u ≠ v ∧
        ∃ c : Fin k, c ∈ MissingColors G phi u ∧
          c ∈ MissingColors G phi v := by
    simp only [ColoredVertexSetElementary, not_forall, Classical.not_imp,
      not_forall, Classical.not_imp, not_forall, Classical.not_imp] at hnot
    rcases hnot with ⟨u, hu, v, hv, huv, hd⟩
    rcases Finset.not_disjoint_iff.mp hd with ⟨beta, hbu, hbv⟩
    exact ⟨u, hu, v, hv, huv, beta, hbu, hbv⟩
  obtain ⟨u, hu, v, hv, huv, beta, hbu, hbv⟩ := hcommon
  have hlast_or_prefix (w : V) (hw : w ∈ TreeSequenceVertexSet T) :
      w = T.vertex (Fin.last T.length) ∨ w ∈ TreeSequenceVertexSet P := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and] at hw ⊢
    obtain ⟨i, hi⟩ := hw
    by_cases hival : i.val = T.length
    · left
      rw [← hi]
      congr 1
      exact Fin.ext hival
    · right
      let q : Fin (P.length + 1) := ⟨i.val, by rw [hP_length]; omega⟩
      refine ⟨q, ?_⟩
      have hq := hPprefix.2.1 q
      have hqi : Fin.castLE (Nat.succ_le_succ hPprefix.1) q = i := by
        apply Fin.ext
        rfl
      rw [hqi] at hq
      exact hq.symm.trans hi
  have hbeta_last : beta ∈ MissingColors G phi (T.vertex (Fin.last T.length)) := by
    rcases hlast_or_prefix u hu with huLast | huPrefix
    · simpa [huLast] using hbu
    · rcases hlast_or_prefix v hv with hvLast | hvPrefix
      · simpa [hvLast] using hbv
      · have hd := hPelementary huPrefix hvPrefix
          (by intro he; exact huv (he ▸ rfl))
        exact (Finset.disjoint_left.mp hd) hbu hbv |>.elim
  by_cases hsmall : ∃ j : Fin (T.length + 1),
      j.val + 2 ≤ T.length ∧
      beta ∈ MissingColors G phi (T.vertex j)
  · obtain ⟨j, hj, hbeta_j⟩ := hsmall
    refine ⟨phi, beta, j, hmin, ?_, hpgamma, hj, hbeta_j, hbeta_last⟩
    simpa [hlastval] using hrgamma
  · have hlast_index : ∀ i : Fin (T.length + 1),
        beta ∈ MissingColors G phi (T.vertex i) →
        i.val = T.length - 1 ∨ i.val = T.length := by
      intro i hi
      by_cases he : i.val = T.length
      · exact Or.inr he
      · left
        by_contra hne
        exact hsmall ⟨i, by omega, hi⟩
    have hbeta_pen : beta ∈ MissingColors G phi (T.vertex
        ⟨T.length - 1, by omega⟩) := by
      rcases hlast_or_prefix u hu with huLast | huPrefix
      · rcases hlast_or_prefix v hv with hvLast | hvPrefix
        · exact (huv (huLast.trans hvLast.symm)).elim
        · have hvindex : ∃ i : Fin (T.length + 1),
              i.val = T.length - 1 ∧ T.vertex i = v := by
            simp only [TreeSequenceVertexSet, Finset.mem_image,
              Finset.mem_univ, true_and] at hvPrefix
            obtain ⟨i, hi⟩ := hvPrefix
            let ii : Fin (T.length + 1) := ⟨i.val, by omega⟩
            have hq := hPprefix.2.1 i
            have heq : Fin.castLE (Nat.succ_le_succ hPprefix.1) i = ii := by
              apply Fin.ext
              rfl
            rw [heq] at hq
            have hidx := hlast_index ii (by
              rw [hq, hi]
              exact hbv)
            rcases hidx with hidx | hidx
            · exact ⟨ii, hidx, hq.trans hi⟩
            · have hiT : i.val < T.length := by
                have hh := i.isLt
                simp [hP_length] at hh
                omega
              have hii : ii.val = i.val := rfl
              have hiiT : ii.val < T.length := by simpa [ii] using hiT
              omega
          obtain ⟨i, hi, hiv⟩ := hvindex
          have hlastEq : T.vertex i = T.vertex ⟨T.length - 1, by omega⟩ := by
            apply congrArg T.vertex
            apply Fin.ext
            simpa using hi
          have hvlast : v = T.vertex ⟨T.length - 1, by omega⟩ := hiv.symm.trans hlastEq
          simpa [hvlast] using hbv
      · rcases hlast_or_prefix v hv with hvLast | hvPrefix
        · have huindex : ∃ i : Fin (T.length + 1),
              i.val = T.length - 1 ∧ T.vertex i = u := by
            simp only [TreeSequenceVertexSet, Finset.mem_image,
              Finset.mem_univ, true_and] at huPrefix
            obtain ⟨i, hi⟩ := huPrefix
            let ii : Fin (T.length + 1) := ⟨i.val, by omega⟩
            have hq := hPprefix.2.1 i
            have heq : Fin.castLE (Nat.succ_le_succ hPprefix.1) i = ii := by
              apply Fin.ext
              rfl
            rw [heq] at hq
            have hidx := hlast_index ii (by
              rw [hq, hi]
              exact hbu)
            rcases hidx with hidx | hidx
            · exact ⟨ii, hidx, hq.trans hi⟩
            · have hiT : i.val < T.length := by
                have hh := i.isLt
                simp [hP_length] at hh
                omega
              have hii : ii.val = i.val := rfl
              have hiiT : ii.val < T.length := by simpa [ii] using hiT
              omega
          obtain ⟨i, hi, hiv⟩ := huindex
          have hlastEq : T.vertex i = T.vertex ⟨T.length - 1, by omega⟩ := by
            apply congrArg T.vertex
            apply Fin.ext
            simpa using hi
          have hulast : u = T.vertex ⟨T.length - 1, by omega⟩ := hiv.symm.trans hlastEq
          simpa [hulast] using hbu
        · exact (Finset.disjoint_left.mp
            (hPelementary huPrefix hvPrefix
              (by intro he; exact huv (he ▸ rfl)))) hbu hbv |>.elim
    have hbeta_unused : TreeColorUnusedThrough phi T beta
        ⟨T.length - 1, by omega⟩ := by
      intro s hs1 hsj
      intro hcolor
      rcases hbad.2.1 s hs1 with ⟨i, c, hc, hmiss⟩
      have hcb : beta = c := by simpa [hcolor] using hc
      subst c
      have hslt : s.val < T.length - 1 := by simpa using hsj
      have his : i.val ≤ s.val := Nat.le_of_lt_succ i.isLt
      have hilt : i.val < T.length - 1 := by omega
      have hvne : T.vertex (Fin.castLT i
            (Nat.lt_trans i.isLt (Nat.succ_lt_succ s.isLt))) ≠
            T.vertex ⟨T.length - 1, by omega⟩ := by
        intro he
        have he' := T.vertex_injective he
        have hiVal := congrArg Fin.val he'
        have hcast : (Fin.castLT i
            (Nat.lt_trans i.isLt (Nat.succ_lt_succ s.isLt))).val = i.val := rfl
        have hcast : (Fin.castLT i
            (Nat.lt_trans i.isLt (Nat.succ_lt_succ s.isLt))).val = i.val := rfl
        omega
      have hd := hPelementary
          (by rw [TreeSequenceVertexSet]
              exact Finset.mem_image.mpr ⟨
                ⟨i.val, by omega⟩, Finset.mem_univ _, by
                  apply congrArg T.vertex; apply Fin.ext; rfl⟩)
          (by rw [TreeSequenceVertexSet]
              exact Finset.mem_image.mpr ⟨
                ⟨T.length - 1, by omega⟩, Finset.mem_univ _, rfl⟩) hvne
      exact (Finset.disjoint_left.mp hd) hmiss hbeta_pen
    have hfree4 : 4 ≤ (TreeFreeColors phi
        (TreeSequencePrefix T (T.length - 2) (by omega) (by omega))).card :=
      TashTreeFourUnusedColors G k e0 phi T hmin (T.length - 2) (by omega) (by omega)
    let Q := TreeSequencePrefix T (T.length - 2) (by omega) (by omega)
    have hfree4' : 4 ≤ (TreeFreeColors phi Q).card := by simpa [Q] using hfree4
    let freeMinusBeta := (TreeFreeColors phi Q).erase beta
    have hfreeMinus : 3 ≤ freeMinusBeta.card := by
      have hc : (TreeFreeColors phi Q).card - 1 ≤ freeMinusBeta.card := by
        simpa [freeMinusBeta] using
          (Finset.pred_card_le_card_erase :
            (TreeFreeColors phi Q).card - 1 ≤ freeMinusBeta.card)
      omega
    let freeMinusGamma := freeMinusBeta.erase gamma
    have hfreeMinusGamma : 2 ≤ freeMinusGamma.card := by
      have hc : freeMinusBeta.card - 1 ≤ freeMinusGamma.card := by
        simpa [freeMinusGamma] using
          (Finset.pred_card_le_card_erase : freeMinusBeta.card - 1 ≤ freeMinusGamma.card)
      omega
    let edgeColor := (phi (T.edge ⟨T.length - 2, by omega⟩)).getD beta
    let freeFinal := freeMinusGamma.erase edgeColor
    have hfreeFinal : 1 ≤ freeFinal.card := by
      have hc : freeMinusGamma.card - 1 ≤ freeFinal.card := by
        simpa [freeFinal] using
          (Finset.pred_card_le_card_erase : freeMinusGamma.card - 1 ≤ freeFinal.card)
      omega
    obtain ⟨alpha, halpha⟩ := Finset.card_pos.mp hfreeFinal
    have halpha_ne_gamma : alpha ≠ gamma :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp halpha).2).1
    have halpha_ne_edge : alpha ≠ edgeColor := (Finset.mem_erase.mp halpha).1
    have halpha_ne_beta : alpha ≠ beta := by
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp
        (Finset.mem_erase.mp halpha).2).2).1
    have halpha_free : alpha ∈ TreeFreeColors phi Q :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp
        (Finset.mem_erase.mp halpha).2).2).2
    have halpha_missing : alpha ∈ TreeMissingColors phi Q := by
      exact (Finset.mem_sdiff.mp halpha_free).1
    obtain ⟨m, hmQ, hma⟩ := by
      rw [TreeMissingColors] at halpha_missing
      simpa only [Finset.mem_biUnion] using halpha_missing
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and] at hmQ
    obtain ⟨mi, hmi⟩ := hmQ
    have hmq : mi.val + 2 ≤ T.length := by
      have hm_lt : mi.val < Q.length + 1 := mi.isLt
      have hQlen : Q.length = T.length - 2 := rfl
      omega
    have hmaT : alpha ∈ MissingColors G phi (T.vertex
        ⟨mi.val, by omega⟩) := by
      have hqv := hmi
      simp [Q] at hqv
      have hQle : Q.length ≤ T.length := by
        change T.length - 2 ≤ T.length
        omega
      have hqv' : T.vertex ⟨mi.val, by omega⟩ = m := by
        simpa [Q, TreeSequencePrefix, Fin.castLE, Fin.castLT] using hmi
      rw [hqv']
      exact hma
    have halpha_unused : TreeColorUnusedThrough phi T alpha
        ⟨T.length - 1, by omega⟩ := by
      intro s hs1 hsj
      by_cases hsLast : s.val = T.length - 1
      · intro heq
        have hs_eq : s = ⟨T.length - 1, by omega⟩ := by
          apply Fin.ext
          exact hsLast
        rw [hs_eq] at heq
        have hr_eq : r = ⟨T.length - 1, by omega⟩ := by
          apply Fin.ext
          exact hlastval
        rw [hr_eq] at hrgamma
        have hh : some alpha = some gamma := heq.symm.trans hrgamma
        exact halpha_ne_gamma (Option.some.inj hh)
      · by_cases hsSecond : s.val = T.length - 2
        · intro heq
          have hs_eq : s = ⟨T.length - 2, by omega⟩ := by
            apply Fin.ext
            exact hsSecond
          rw [hs_eq] at heq
          cases hval : phi (T.edge ⟨T.length - 2, by omega⟩) with
          | none => simp [hval] at heq
          | some c =>
            have hc : phi (T.edge ⟨T.length - 2, by omega⟩) = some c := hval
            have : edgeColor = c := by simp [edgeColor, hc]
            have hac : alpha = c := Option.some.inj (heq.symm.trans hc)
            exact halpha_ne_edge (hac.trans this.symm)
        · have hsQ : s.val < Q.length := by
            have hQlen : Q.length = T.length - 2 := rfl
            have hsle : s.val ≤ T.length - 2 := by omega
            have hslt2 : s.val < T.length - 2 := by
              by_contra hn
              have he : s.val = T.length - 2 := by omega
              exact hsSecond he
            simpa only [hQlen] using hslt2
          have husedQ : alpha ∉ TreeUsedColors phi Q :=
            (Finset.mem_sdiff.mp halpha_free).2
          intro heq
          apply husedQ
          simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨⟨s.val, by omega⟩, hs1, by
            simpa [Q, TreeSequencePrefix, Fin.castLE] using heq⟩
    have hmi_lt : mi.val < T.length - 1 := by omega
    have hswap := TashTreeControlledInterchange G k e0 phi T hmin
      ⟨mi.val, by omega⟩
      ⟨T.length - 1, by show T.length - 1 < T.length + 1; omega⟩
      hmi_lt (by show T.length - 1 < T.length; omega)
      alpha beta (by exact halpha_ne_beta) hmaT hbeta_pen halpha_unused hbeta_unused
    dsimp only at hswap
    let phi3 := TwoColorComponentSwap G phi alpha beta
      (Sum.inl (T.vertex ⟨T.length - 1, by omega⟩))
    have hmin3 := hswap.2.2.2.2.2.2.2.2
    have hbeta_last3 : beta ∈ MissingColors G phi3
        (T.vertex (Fin.last T.length)) := by
      have houtside : Sum.inl (T.vertex (Fin.last T.length)) ∉
          TwoColorComponent G phi alpha beta
            (Sum.inl (T.vertex ⟨T.length - 1, by omega⟩)) := by
        by_contra hin
        obtain ⟨a, b, path, hpath, hsupport⟩ :=
          TwoColorComponentSpanningPath G phi alpha beta hproper
            (Sum.inl (T.vertex ⟨T.length - 1, by omega⟩))
        have support_of_component {x : Sum V E} (hx : x ∈
            TwoColorComponent G phi alpha beta
              (Sum.inl (T.vertex ⟨T.length - 1, by omega⟩))) :
            x ∈ path.support := by
          change x ∈ {y | y ∈ path.support}
          rw [hsupport]
          exact hx
        have endpoint_of_subsingleton {x : Sum V E} (hx : x ∈
            TwoColorComponent G phi alpha beta
              (Sum.inl (T.vertex ⟨T.length - 1, by omega⟩)))
            (hxSub : Set.Subsingleton
              ((TwoColorIncidenceGraph G phi alpha beta).neighborSet x)) :
            x = a ∨ x = b := by
          by_contra hend
          push_neg at hend
          exact (hpath.isTrail.not_mem_support_of_subsingleton_neighborSet
            hend.1 hend.2 hxSub) (support_of_component hx)
        have hmEnd := endpoint_of_subsingleton hswap.2.1 hswap.2.2.1
        have hpEnd := endpoint_of_subsingleton
          (by change Sum.inl (T.vertex ⟨T.length - 1, by omega⟩) ∈
              TwoColorComponent G phi alpha beta
                (Sum.inl (T.vertex ⟨T.length - 1, by omega⟩))
              change Sum.inl (T.vertex ⟨T.length - 1, by omega⟩) ∈
                ((TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk
                  (Sum.inl (T.vertex ⟨T.length - 1, by omega⟩))).supp
              rw [SimpleGraph.ConnectedComponent.mem_supp_iff])
          hswap.2.2.2.1
        have hlSub : Set.Subsingleton
            ((TwoColorIncidenceGraph G phi alpha beta).neighborSet
              (Sum.inl (T.vertex (Fin.last T.length)))) := by
          letI : Fintype
              ((TwoColorIncidenceGraph G phi beta alpha).neighborSet
                (Sum.inl (T.vertex (Fin.last T.length)))) := Fintype.ofFinite _
          have hd := MissingColorIncidenceEndpoint G phi beta alpha
            halpha_ne_beta.symm hproper (T.vertex (Fin.last T.length)) hbeta_last
          intro x hx y hy
          have hx' : x ∈ (TwoColorIncidenceGraph G phi beta alpha).neighborFinset
              (Sum.inl (T.vertex (Fin.last T.length))) := by
            apply (SimpleGraph.mem_neighborFinset
              (TwoColorIncidenceGraph G phi beta alpha)
              (Sum.inl (T.vertex (Fin.last T.length))) x).2
            cases x <;> simpa [TwoColorIncidenceGraph, or_comm] using hx
          have hy' : y ∈ (TwoColorIncidenceGraph G phi beta alpha).neighborFinset
              (Sum.inl (T.vertex (Fin.last T.length))) := by
            apply (SimpleGraph.mem_neighborFinset
              (TwoColorIncidenceGraph G phi beta alpha)
              (Sum.inl (T.vertex (Fin.last T.length))) y).2
            cases y <;> simpa [TwoColorIncidenceGraph, or_comm] using hy
          have hc : ((TwoColorIncidenceGraph G phi beta alpha).neighborFinset
              (Sum.inl (T.vertex (Fin.last T.length)))).card ≤ 1 := by
            rw [SimpleGraph.card_neighborFinset_eq_degree]
            exact hd
          exact (Finset.card_le_one.mp hc) x hx' y hy'
        have hlEnd := endpoint_of_subsingleton hin hlSub
        have hm_ne_last : (Sum.inl (T.vertex ⟨mi.val, by omega⟩) : Sum V E) ≠
            Sum.inl (T.vertex (Fin.last T.length)) := by
          intro he
          have hv : T.vertex ⟨mi.val, by omega⟩ =
              T.vertex (Fin.last T.length) := by simpa using he
          have hh := congrArg Fin.val (T.vertex_injective hv)
          have hmiVal : (⟨mi.val, by omega⟩ : Fin (T.length + 1)).val = mi.val := rfl
          have hlastVal : (Fin.last T.length).val = T.length := rfl
          omega
        have hp_ne_last : (Sum.inl (T.vertex ⟨T.length - 1, by omega⟩) : Sum V E) ≠
            Sum.inl (T.vertex (Fin.last T.length)) := by
          intro he
          have hv : T.vertex ⟨T.length - 1, by omega⟩ =
              T.vertex (Fin.last T.length) := by simpa using he
          have hh := congrArg Fin.val (T.vertex_injective hv)
          have hpenVal : (⟨T.length - 1, by omega⟩ : Fin (T.length + 1)).val = T.length - 1 := rfl
          have hlastVal : (Fin.last T.length).val = T.length := rfl
          omega
        have hm_ne_pen : (Sum.inl (T.vertex ⟨mi.val, by omega⟩) : Sum V E) ≠
            Sum.inl (T.vertex ⟨T.length - 1, by omega⟩) := by
          intro he
          have hv : T.vertex ⟨mi.val, by omega⟩ =
              T.vertex ⟨T.length - 1, by omega⟩ := by simpa using he
          have hh := congrArg Fin.val (T.vertex_injective hv)
          have hmiVal : (⟨mi.val, by omega⟩ : Fin (T.length + 1)).val = mi.val := rfl
          have hpenVal : (⟨T.length - 1, by omega⟩ : Fin (T.length + 1)).val = T.length - 1 := rfl
          omega
        have endpoint_is_m_or_pen {x : Sum V E} (hx : x = a ∨ x = b) :
            x = Sum.inl (T.vertex ⟨mi.val, by omega⟩) ∨
            x = Sum.inl (T.vertex ⟨T.length - 1, by omega⟩) := by
          rcases hmEnd with hmA | hmB <;> rcases hpEnd with hpA | hpB
          · exact False.elim (hm_ne_pen (hmA.trans hpA.symm))
          · rcases hx with hxa | hxb
            · exact Or.inl (hxa.trans hmA.symm)
            · exact Or.inr (hxb.trans hpB.symm)
          · rcases hx with hxa | hxb
            · exact Or.inr (hxa.trans hpA.symm)
            · exact Or.inl (hxb.trans hmB.symm)
          · exact False.elim (hm_ne_pen (hmB.trans hpB.symm))
        rcases endpoint_is_m_or_pen hlEnd with hml | hpl
        · exact hm_ne_last hml.symm
        · exact hp_ne_last hpl.symm
      have hmiss := TwoColorComponentSwapMissingBehavior G phi alpha beta
        halpha_ne_beta hproper
        (Sum.inl (T.vertex ⟨T.length - 1, by omega⟩))
      dsimp only at hmiss
      exact (hmiss.1 _ houtside) ▸ hbeta_last
    have hbeta_ne_gamma : beta ≠ gamma := by
      intro he
      subst beta
      obtain ⟨ii, hii⟩ := T.attaches r
      have hrs : r.succ = Fin.last T.length := by
        apply Fin.ext
        simpa using hr
      have hinc : Incident G (T.vertex (Fin.last T.length)) (T.edge r) := by
        rw [Incident, hii]
        simp [hrs]
      have hnotpresent : gamma ∉ PresentColors G phi (T.vertex (Fin.last T.length)) := by
        simpa [MissingColors] using hbeta_last
      apply hnotpresent
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨T.edge r, hinc, hrgamma⟩
    refine ⟨phi3, beta, ⟨mi.val, by omega⟩, hmin3, ?_, ?_, hmq,
      hswap.2.2.2.2.1, hbeta_last3⟩
    · have hr_eq : r = ⟨T.length - 1, by omega⟩ := by
        apply Fin.ext
        exact hlastval
      rw [hr_eq] at hrgamma ⊢
      by_cases hm : Sum.inr (T.edge ⟨T.length - 1, by omega⟩) ∈
          TwoColorComponent G phi alpha beta
            (Sum.inl (T.vertex ⟨T.length - 1, by omega⟩))
      · simp [phi3, TwoColorComponentSwap, hm, hrgamma,
            Ne.symm halpha_ne_gamma, Ne.symm hbeta_ne_gamma]
      · simp [phi3, TwoColorComponentSwap, hm, hrgamma,
          Ne.symm halpha_ne_gamma, Ne.symm hbeta_ne_gamma]
    · have hp_eq : p = ⟨T.length - 1, by omega⟩ := by
        apply Fin.ext
        exact hpval
      have hpold : gamma ∈ PresentColors G phi
          (T.vertex ⟨T.length - 1, by omega⟩) := by
        rw [hp_eq] at hpgamma
        exact hpgamma
      rcases (by simpa [PresentColors] using hpold) with ⟨e, he, hc⟩
      rw [hp_eq]
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨e, he, by
        by_cases hm : Sum.inr e ∈ TwoColorComponent G phi alpha beta
            (Sum.inl (T.vertex ⟨T.length - 1, by omega⟩))
        · dsimp [phi3]
          simp [TwoColorComponentSwap, hc, hm, Ne.symm halpha_ne_gamma,
            Ne.symm hbeta_ne_gamma]
        · dsimp [phi3]
          simp [TwoColorComponentSwap, hc, hm, Ne.symm halpha_ne_gamma,
            Ne.symm hbeta_ne_gamma]⟩
