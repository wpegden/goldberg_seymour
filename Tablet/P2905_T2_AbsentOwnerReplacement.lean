import Tablet.StableChangeCasesOneTwoFullTail
import Tablet.ChangeLemma
import Tablet.GoodHierarchyReservedDisjoint
import Tablet.NineN
import Tablet.HierarchyReplacementPresentationTrans
import Tablet.P2905_T2_ElementaryTerminalComponent
import Tablet.TwoColorComponentSwapMissingBehavior

-- [TABLET NODE: P2905_T2_AbsentOwnerReplacement]
theorem P2905_T2_AbsentOwnerReplacement {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (hpathLower : 2 ≤ HierarchyPathNumber C.hierarchy)
    (hpathUpper : HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C)
    (alpha : Fin k)
    (hterminal : alpha ∈ MissingColors G phi (T.vertex (Fin.last T.length)))
    (hstar : alpha ∈ TreeMissingColors phi (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)))
    (eta : Fin k) (heta : eta ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount))
    (hgamma : alpha ∈ C.good.gamma (Fin.last C.hierarchy.dividerCount) eta)
    (habsent : eta ∉ TreeMissingColors phi
      (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1))) :
    ∃ P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx,
      ∃ beta : Fin k,
        beta ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)) ∧
        beta ∈ TreeMissingColors P.coloring
          (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 2)) ∧
        (let H := P.counterexample.hierarchy
        let q := Fin.last H.dividerCount
        let Tn := P.corresponding.replacementETT.series.data.tree
          (Fin.last P.corresponding.replacementETT.rounds).castSucc
        beta ∉ (HierarchyStoredColorsAt H q).biUnion
          (P.counterexample.good.gamma q) ∪
          ((TreeSequenceVertexSet P.replacementBase.core \
              TreeSequenceVertexSet Tn).biUnion
            fun v => MissingColors G P.coloring v)) := by
-- BODY
  classical
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let ell := HierarchyFullTailLength C
  let X := HierarchyFullTailPrefix C (ell - 2)
  let B := HierarchyFullTailPrefix C (ell - 1)
  let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
  let D := HierarchyStoredColorsAt H q
  let Gamma := D.biUnion (C.good.gamma q)
  let M0 := (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet Tn).biUnion
    fun v => MissingColors G phi v
  have htail : 3 ≤ ell := by
    change 2 ≤ HierarchyPathNumber H at hpathLower
    change HierarchyPathNumber H < ell at hpathUpper
    omega
  have htailA : 3 ≤ T.length - A.length := by
    simpa [ell, HierarchyFullTailLength, H] using htail
  have hA : TreeSequenceInitialSegment A T := by
    have starNext (i : Fin (H.dividerCount + 1)) :
        TreeSequenceInitialSegment (HierarchyStarredStage H i) (H.stage i.succ) :=
      Fin.cases H.coreInsideFirst (fun i => H.nested i.succ) i
    simpa only [Fin.succ_last, H.terminalStage] using
      starNext (Fin.last H.dividerCount)
  have hell : ell = T.length - A.length := rfl
  have hBprefix : TreeSequenceInitialSegment B T := by
    exact ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have hXprefix : TreeSequenceInitialSegment X T := by
    exact ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have hlenB : B.length = T.length - 1 := by
    change min (A.length + (ell - 1)) T.length = T.length - 1
    simp only [ell, HierarchyFullTailLength, H] at *
    omega
  have hlenX : X.length = T.length - 2 := by
    change min (A.length + (ell - 2)) T.length = T.length - 2
    simp only [ell, HierarchyFullTailLength, H] at *
    omega
  have commonPrefix {S U W : TreeSequence G e0}
      (hSW : TreeSequenceInitialSegment S W)
      (hUW : TreeSequenceInitialSegment U W) (hlen : S.length ≤ U.length) :
      TreeSequenceInitialSegment S U := by
    refine ⟨hlen, ?_, ?_⟩
    · intro i
      exact (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hlen) i)).symm.trans (hSW.2.1 i)
    · intro i
      exact (hUW.2.2 (Fin.castLE hlen i)).symm.trans (hSW.2.2 i)
  have hAB : TreeSequenceInitialSegment A B := by
    apply commonPrefix hA hBprefix
    rw [hlenB]
    omega
  have hElem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) := by
    exact HierarchyCounterexamplePenultimateElementary G k e0 input T phi ett base C
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality ctx.largeMissingSet
  have hcoreA : TreeSequenceVertexSet base.core ⊆ TreeSequenceVertexSet A := by
    by_cases hz : H.dividerCount = 0
    · have hq : q = 0 := Fin.ext (by simp [q, hz])
      simp [A, HierarchyStarredStage, hq]
    · let r : Fin H.dividerCount := ⟨H.dividerCount - 1, by omega⟩
      have hq : q = r.succ := by apply Fin.ext; simp [q, r]; omega
      have hAs : A = H.stage r.succ.castSucc := by
        change HierarchyStarredStage H q = _
        rw [hq]
        rfl
      rw [hAs]
      have stageMono : Monotone (fun j : Fin (H.dividerCount + 2) =>
          TreeSequenceVertexSet (H.stage j)) := by
        apply Fin.monotone_iff_le_succ.mpr
        intro j
        exact TreeSequenceInitialSegmentVertexSetSubset (H.nested j)
      exact (TreeSequenceInitialSegmentVertexSetSubset H.coreInsideFirst).trans
        (stageMono (by change 1 ≤ r.val + 1; omega))
  have hTnCore : TreeSequenceVertexSet Tn ⊆ TreeSequenceVertexSet base.core := by
    by_cases hp : ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE
    · obtain ⟨_, _, ⟨u⟩⟩ := base.parallel hp
      exact TreeSequenceInitialSegmentVertexSetSubset u.leftSegment
    · have hc := base.nonparallel hp
      change base.core = Tn at hc
      rw [hc]
  have hcoreB : TreeSequenceVertexSet base.core ⊆ TreeSequenceVertexSet B := by
    exact hcoreA.trans (TreeSequenceInitialSegmentVertexSetSubset
      (commonPrefix hA hBprefix (by rw [hlenB]; omega)))
  have hTnB : TreeSequenceVertexSet Tn ⊆ TreeSequenceVertexSet B := hTnCore.trans hcoreB
  have hownerAbsent : eta ∉ TreeMissingColors phi B := by
    simpa [B, ell] using habsent
  have hfirstEta : HierarchyFirstMissingPosition phi T eta = Fin.last T.length := by
    classical
    unfold HierarchyFirstMissingPosition
    dsimp only
    split
    · rename_i hc
      have candidateLast (i : Fin (T.length + 1))
          (hi : i ∈ Finset.univ.filter
            (fun i => eta ∈ MissingColors G phi (T.vertex i))) :
          i = Fin.last T.length := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        apply Fin.ext
        by_cases heq : i.val = T.length
        · exact heq
        · have hlt : i.val < T.length := by have := i.isLt; omega
          have hiBval : i.val < B.length + 1 := by rw [hlenB]; omega
          let j : Fin (B.length + 1) := ⟨i.val, hiBval⟩
          have hij : Fin.castLE (Nat.succ_le_succ hBprefix.1) j = i := Fin.ext rfl
          have hvB : T.vertex i ∈ TreeSequenceVertexSet B := by
            simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
            exact ⟨j, by rw [← hBprefix.2.1 j, hij]⟩
          have hmB : eta ∈ TreeMissingColors phi B :=
            Finset.mem_biUnion.mpr ⟨T.vertex i, hvB, hi⟩
          exact False.elim (hownerAbsent hmB)
      have hm := Finset.min'_mem
        (Finset.univ.filter fun i : Fin (T.length + 1) =>
          eta ∈ MissingColors G phi (T.vertex i)) hc
      rw [candidateLast _ hm]
    · rfl
  have hAlphaAvoid : ∀ r : Fin T.length, A.length ≤ r.val →
      phi (T.edge r) ≠ some alpha := by
    intro r hr hcol
    have havoid := C.good.avoidance q eta heta
    have hseg : alpha ∉ HierarchySegmentColors H q eta := by
      exact (Finset.mem_sdiff.mp (havoid hgamma)).2
    have hqstage : H.stage q.succ = T := by
      simpa only [q, Fin.succ_last] using H.terminalStage
    have hTedge : A.length ≤ r.val ∧ r.val < min (HierarchyFirstMissingPosition phi T eta).val
        (H.stage q.succ).length := by
      rw [hfirstEta, Fin.val_last, hqstage]
      simp only [min_self]
      exact ⟨hr, r.isLt⟩
    have : alpha ∈ HierarchySegmentColors H q eta := by
      let hlen : (H.stage q.succ).length = T.length := congrArg TreeSequence.length hqstage
      let s : Fin (H.stage q.succ).length := Fin.cast hlen.symm r
      have hsval : s.val = r.val := rfl
      have hstageT : TreeSequenceInitialSegment (H.stage q.succ) T := by
        rw [hqstage]
        exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
      have hcast : Fin.castLE hstageT.1 s = r := by
        apply Fin.ext
        rfl
      have hedge := hstageT.2.2 s
      rw [hcast] at hedge
      have hcol' : phi ((H.stage q.succ).edge s) = some alpha := by
        rw [← hedge]
        exact hcol
      simp only [HierarchySegmentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨s, ?_⟩
      rw [hfirstEta, Fin.val_last]
      refine ⟨?_, ?_, hcol'⟩
      · simpa [hsval] using hr
      · rw [hsval]
        have hslt := s.isLt
        have hrl := r.isLt
        omega
    exact hseg this
  have hNineIndex : ell - 2 < ell := by omega
  have hNine := NineN G k e0 input T phi ett C.positive base H C.good hElem
    ctx.largeMissingSet (ell - 2) hNineIndex
  let U := (Finset.univ : Finset (Fin k)).filter fun c =>
    ∃ r : Fin T.length,
      A.length ≤ r.val ∧ r.val < A.length + (ell - 2) ∧ phi (T.edge r) = some c
  let Avail := (TreeMissingColors phi X \ M0) \ U
  have hNineAt := hNine
  dsimp [Tn, q, A, ell, HierarchyFullTailLength] at hNineAt
  have hNi := hNineAt
  have hNiCard : 2 * ett.rounds + 11 ≤ Avail.card := by
    change 2 * ett.rounds + 11 ≤ Avail.card
    exact hNi.1
  have hGoodAvoid := GoodHierarchyReservedDisjoint C.good q
  have hGammaD : Disjoint Gamma D := by
    simpa [Gamma, D] using hGoodAvoid.2
  have hEtaNotA : eta ∉ TreeMissingColors phi A := by
    intro hm
    have hD := (Finset.mem_sdiff.mp heta).2
    exact hD hm
  have hAlphaNotD : alpha ∉ D := by
    intro ha
    have hAlphaGamma : alpha ∈ Gamma := Finset.mem_biUnion.mpr ⟨eta, heta, hgamma⟩
    exact Finset.disjoint_left.mp hGammaD hAlphaGamma ha
  let r0 : Fin T.length := ⟨T.length - 2, by have := htailA; omega⟩
  let r1 : Fin T.length := ⟨T.length - 1, by have := htailA; omega⟩
  let N := (phi (T.edge r0)).toList.toFinset ∪ (phi (T.edge r1)).toList.toFinset
  have hNcard : N.card ≤ 2 := by
    dsimp [N]
    calc
      _ ≤ (phi (T.edge r0)).toList.length + (phi (T.edge r1)).toList.length :=
        (Finset.card_union_le _ _).trans (Nat.add_le_add
          (List.toFinset_card_le _) (List.toFinset_card_le _))
      _ ≤ 2 := by
        cases phi (T.edge r0) <;> cases phi (T.edge r1) <;> simp
  have hr0val : r0.val = T.length - 2 := by simp [r0]
  have hr1val : r1.val = T.length - 1 := by simp [r1]
  have hSuffixN : ∀ (c : Fin k) (r : Fin T.length), X.length ≤ r.val →
      phi (T.edge r) = some c → c ∈ N := by
    intro c r hr hc
    have hindex : r.val = r0.val ∨ r.val = r1.val := by
      have := hlenX
      omega
    rcases hindex with hindex | hindex
    · have hr0 : r = r0 := Fin.ext hindex
      subst r
      simp [N, hc]
    · have hr1 : r = r1 := Fin.ext hindex
      subst r
      simp [N, hc]
  let Free := Avail \ (Gamma ∪ D)
  have hNineSmall := hNi.2
  change (Avail \ (Gamma ∪ D)).card ≤ 4 →
    ∃ rho : Fin 7 → Fin k, Function.Injective rho ∧
      ∀ i, rho i ∈ D ∧ rho i ∈ TreeMissingColors phi X ∧
        Disjoint (C.good.gamma q (rho i) ∪ {rho i}) U at hNineSmall
  have hbetaExists : ∃ beta : Fin k,
      beta ∈ TreeMissingColors phi X ∧ beta ∉ M0 ∧ beta ∉ Gamma ∧
        beta ∉ U ∧ beta ∉ N := by
    by_cases hlarge : 5 ≤ Free.card
    · have hremain : (Free \ N).Nonempty := by
        apply Finset.card_pos.mp
        have hc := Finset.card_le_card_sdiff_add_card (s := Free) (t := N)
        omega
      obtain ⟨beta, hb⟩ := hremain
      have hbfree := (Finset.mem_sdiff.mp hb).1
      have hbN := (Finset.mem_sdiff.mp hb).2
      obtain ⟨hbAvail, hbGD⟩ := Finset.mem_sdiff.mp hbfree
      obtain ⟨hbMissExtra, hbU⟩ := Finset.mem_sdiff.mp hbAvail
      obtain ⟨hbMiss, hbExtra⟩ := Finset.mem_sdiff.mp hbMissExtra
      refine ⟨beta, hbMiss, hbExtra, ?_, hbU, hbN⟩
      · intro hb
        exact hbGD (Finset.mem_union_left _ hb)
    · obtain ⟨rho, hinj, hrho⟩ := hNineSmall (by change Free.card ≤ 4; omega)
      let block := fun i : Fin 7 => C.good.gamma q (rho i) ∪ {rho i}
      have hblocks : ∀ i j : Fin 7, i ≠ j → Disjoint (block i) (block j) := by
        intro i j hij
        have hneq : rho i ≠ rho j := fun heq => hij (hinj heq)
        rw [Finset.disjoint_left]
        intro c hci hcj
        simp only [block, Finset.mem_union, Finset.mem_singleton] at hci hcj
        rcases hci with hci | hci <;> rcases hcj with hcj | hcj
        · exact Finset.disjoint_left.mp (C.good.disjointPairs q (rho i) (rho j)
            (hrho i).1 (hrho j).1 hneq) hci hcj
        · exact Finset.disjoint_left.mp hGammaD
            (Finset.mem_biUnion.mpr ⟨rho i, (hrho i).1, hci⟩) (hcj.symm ▸ (hrho j).1)
        · exact Finset.disjoint_left.mp hGammaD
            (Finset.mem_biUnion.mpr ⟨rho j, (hrho j).1, hcj⟩) (hci.symm ▸ (hrho i).1)
        · exact hneq (hci.symm.trans hcj)
      have hsomeBlock : ∃ i : Fin 7, Disjoint (block i) N := by
        by_contra hnone
        push_neg at hnone
        let f : Fin 7 → {c // c ∈ N} := fun i =>
          ⟨Classical.choose (Finset.not_disjoint_iff.mp (hnone i)),
            (Classical.choose_spec (Finset.not_disjoint_iff.mp (hnone i))).2⟩
        have hf : Function.Injective f := by
          intro i j hij
          by_contra hne
          have hfi := Classical.choose_spec (Finset.not_disjoint_iff.mp (hnone i))
          have hfj := Classical.choose_spec (Finset.not_disjoint_iff.mp (hnone j))
          have heq : Classical.choose (Finset.not_disjoint_iff.mp (hnone i)) =
              Classical.choose (Finset.not_disjoint_iff.mp (hnone j)) :=
            congrArg Subtype.val hij
          exact (Finset.disjoint_left.mp (hblocks i j hne) hfi.1 (heq ▸ hfj.1))
        have hc := Fintype.card_le_of_injective f hf
        have hcard : Fintype.card {c // c ∈ N} = N.card := Fintype.card_coe N
        rw [hcard] at hc
        have : 7 ≤ 2 := by simpa using hc.trans hNcard
        omega
      obtain ⟨i, hiBlock⟩ := hsomeBlock
      let beta := rho i
      have hbTailMissing : beta ∈ TreeMissingColors phi X := (hrho i).2.1
      have hbD : beta ∈ D := (hrho i).1
      have hbGamma : beta ∉ Gamma := by
        intro hb
        exact (Finset.disjoint_left.mp hGammaD hb hbD)
      have hbM0 : beta ∉ M0 := by
        intro hb
        obtain ⟨v, hv, hmiss⟩ := Finset.mem_biUnion.mp hb
        have hvA : v ∈ TreeSequenceVertexSet A :=
          hcoreA (Finset.mem_sdiff.mp hv).1
        have hbA : beta ∈ TreeMissingColors phi A := Finset.mem_biUnion.mpr ⟨v, hvA, hmiss⟩
        exact (Finset.mem_sdiff.mp hbD).2 hbA
      have hbU : beta ∉ U := by
        intro hbU
        simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hbU
        obtain ⟨r, hr, hlt, hcol⟩ := hbU
        have hblock := (hrho i).2.2
        exact (Finset.disjoint_left.mp hblock
          (Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl))
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, r, hr, hlt, hcol⟩))
      have hbN : beta ∉ N := by
        intro hb
        exact (Finset.disjoint_left.mp hiBlock
          (Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl)) hb)
      refine ⟨beta, hbTailMissing, hbM0, hbGamma, hbU, hbN⟩
  obtain ⟨beta, hbX, hbM0, hbGamma, hbU, hbN⟩ := hbetaExists
  have missingMono (psi : PartialEdgeColoring E k) {S R : TreeSequence G e0}
      (hSR : TreeSequenceInitialSegment S R) :
      TreeMissingColors psi S ⊆ TreeMissingColors psi R := by
    intro c hc
    obtain ⟨v, hv, hmiss⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr
      ⟨v, TreeSequenceInitialSegmentVertexSetSubset hSR hv, hmiss⟩
  have hAX : TreeSequenceInitialSegment A X := commonPrefix hA hXprefix (by
    rw [hlenX]
    omega)
  have hXB : TreeSequenceInitialSegment X B := commonPrefix hXprefix hBprefix (by
    rw [hlenX, hlenB]
    omega)
  have haB : alpha ∈ TreeMissingColors phi B := missingMono phi hAB hstar
  have hbB : beta ∈ TreeMissingColors phi B := missingMono phi hXB hbX
  obtain ⟨ua, hua, hma⟩ := Finset.mem_biUnion.mp hstar
  obtain ⟨uaIdx, huaIdx⟩ :
      ∃ i : Fin (A.length + 1), A.vertex i = ua := by
    simpa only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] using hua
  obtain ⟨ub, hub, hmb⟩ := Finset.mem_biUnion.mp hbX
  obtain ⟨ubIdx, hubIdx⟩ :
      ∃ i : Fin (X.length + 1), X.vertex i = ub := by
    simpa only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] using hub
  have firstLe (c : Fin k) (i : Fin (T.length + 1))
      (hi : c ∈ MissingColors G phi (T.vertex i)) :
      (HierarchyFirstMissingPosition phi T c).val ≤ i.val := by
    let candidates := Finset.univ.filter fun j : Fin (T.length + 1) =>
      c ∈ MissingColors G phi (T.vertex j)
    have hm : i ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    have hn : candidates.Nonempty := ⟨i, hm⟩
    unfold HierarchyFirstMissingPosition
    rw [dif_pos hn]
    have hle := Finset.min'_le candidates i hm
    change (candidates.min' hn).val ≤ i.val at hle
    exact hle
  have firstMem (c : Fin k)
      (hlt : (HierarchyFirstMissingPosition phi T c).val < T.length) :
      c ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T c)) := by
    let candidates := Finset.univ.filter fun j : Fin (T.length + 1) =>
      c ∈ MissingColors G phi (T.vertex j)
    by_cases hn : candidates.Nonempty
    · unfold HierarchyFirstMissingPosition
      rw [dif_pos hn]
      exact (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
    · have hh : (HierarchyFirstMissingPosition phi T c).val = T.length := by
        unfold HierarchyFirstMissingPosition
        rw [dif_neg hn]
        rfl
      omega
  have hiaLe : (HierarchyFirstMissingPosition phi T alpha).val ≤ A.length := by
    let iT := Fin.castLE (Nat.succ_le_succ hA.1) uaIdx
    have hmiss : alpha ∈ MissingColors G phi (T.vertex iT) := by
      rw [hA.2.1 uaIdx, huaIdx]
      exact hma
    have hle := firstLe alpha iT hmiss
    change (HierarchyFirstMissingPosition phi T alpha).val ≤ uaIdx.val at hle
    have hi := uaIdx.isLt
    omega
  have hbetaWitness : beta ∈ MissingColors G phi
      (T.vertex (Fin.castLE (Nat.succ_le_succ hXprefix.1) ubIdx)) := by
    rw [hXprefix.2.1 ubIdx, hubIdx]
    exact hmb
  have hibLe : (HierarchyFirstMissingPosition phi T beta).val ≤
      (Fin.castLE (Nat.succ_le_succ hXprefix.1) ubIdx).val :=
    firstLe beta _ hbetaWitness
  have hibLt : (HierarchyFirstMissingPosition phi T beta).val < T.length := by
    have hidxVal :
        (Fin.castLE (Nat.succ_le_succ hXprefix.1) ubIdx).val = ubIdx.val := rfl
    have huval : ubIdx.val < T.length := by omega
    have hcastLt :
        (Fin.castLE (Nat.succ_le_succ hXprefix.1) ubIdx).val < T.length := by
      rw [hidxVal]
      exact huval
    exact hibLe.trans_lt hcastLt
  have hbetaFirst : beta ∈ MissingColors G phi
      (T.vertex (HierarchyFirstMissingPosition phi T beta)) :=
    firstMem beta hibLt
  let hia := HierarchyFirstMissingPosition phi T alpha
  let hib := HierarchyFirstMissingPosition phi T beta
  have hiaVal : hia.val ≤ A.length := by simpa [hia] using hiaLe
  have hbetaPosAfterA (hbetaNotA : beta ∉ TreeMissingColors phi A) :
      A.length < hib.val := by
    by_contra hle
    have hiA : hib.val ≤ A.length := by omega
    let iA : Fin (A.length + 1) := ⟨hib.val, by omega⟩
    have hidx : Fin.castLE (Nat.succ_le_succ hA.1) iA = hib := Fin.ext rfl
    have vertexMem (S : TreeSequence G e0) (i : Fin (S.length + 1)) :
        S.vertex i ∈ TreeSequenceVertexSet S := by
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨i, rfl⟩
    have hbA : beta ∈ TreeMissingColors phi A := by
      refine Finset.mem_biUnion.mpr ⟨A.vertex iA, vertexMem A iA, ?_⟩
      rw [← hA.2.1 iA, hidx]
      simpa [hib] using hbetaFirst
    exact hbetaNotA hbA
  have horderedUnused :
      (alpha ∉ TreeMissingColors phi A ∨ beta ∉ TreeMissingColors phi A) →
        TreeVertexOrder T (T.vertex hia) (T.vertex hib) ∧
          alpha ∉ (Finset.univ.filter fun c =>
            ∃ t : Fin T.length, A.length ≤ t.val ∧ t.val < hib.val ∧
              phi (T.edge t) = some c) := by
    intro hout
    by_cases hbA : beta ∈ TreeMissingColors phi A
    · rcases hout with hna | hnb
      · exact (hna hstar).elim
      · exact (hnb hbA).elim
    · have hlt : hia.val < hib.val := by
        have := hbetaPosAfterA hbA
        omega
      refine ⟨⟨hia, hib, rfl, rfl, hlt⟩, ?_⟩
      intro ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      obtain ⟨t, htA, _, htc⟩ := ha
      exact hAlphaAvoid t htA htc
  have hne : alpha ≠ beta := by
    intro heq
    exact hbGamma (heq ▸ Finset.mem_biUnion.mpr ⟨eta, heta, hgamma⟩)
  have hchange := ChangeLemma G k e0 input T phi ett base C
    ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
    ctx.lexicographicMinimality hElem ctx.largeMissingSet alpha beta hne
    ⟨haB, hbB⟩ horderedUnused
  have hStageMiss : alpha ∈ HierarchyStageMissingColors H q :=
    (Finset.mem_sdiff.mp (C.good.avoidance q eta heta hgamma)).1
  have hSame : TwoColorComponent G phi alpha beta (Sum.inl (T.vertex hia)) =
      TwoColorComponent G phi alpha beta (Sum.inl (T.vertex hib)) := by
    by_cases hd : 0 < H.dividerCount
    · apply hchange.1
      refine ⟨hd, Or.inl ?_⟩
      let r : Fin H.dividerCount := ⟨H.dividerCount - 1, by omega⟩
      have hq : q = r.succ := by
        apply Fin.ext
        simp [q, r]
        omega
      have hm := hStageMiss
      unfold HierarchyStageMissingColors at hm
      rw [hq] at hm
      change alpha ∈ TreeMissingColors phi (H.stage r.succ.castSucc) at hm
      have hidx : r.succ.castSucc = ⟨H.dividerCount, by omega⟩ := by
        apply Fin.ext
        simp [r]
        omega
      rw [hidx] at hm
      exact hm
    · have hz : H.dividerCount = 0 := by omega
      apply hchange.2.1
      refine ⟨hz, Or.inl ?_⟩
      have hq : q = 0 := Fin.ext (by simp [q, hz])
      have hm := hStageMiss
      unfold HierarchyStageMissingColors at hm
      rw [hq] at hm
      exact hm
  have hiaBound : hia.val ≤ A.length := by simpa [hia] using hiaLe
  have hiaLt : hia.val < T.length := by
    have hAshort : A.length < T.length := by
      have h := htailA
      clear * - h
      omega
    exact Nat.lt_of_le_of_lt hiaBound hAshort
  have hAlphaFirst := firstMem alpha hiaLt
  have huB : T.vertex hia ∈ TreeSequenceVertexSet B := by
    let iA : Fin (A.length + 1) := ⟨hia.val, by omega⟩
    have hcast : Fin.castLE (Nat.succ_le_succ hA.1) iA = hia := Fin.ext rfl
    have hvA : A.vertex iA ∈ TreeSequenceVertexSet A := by
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨iA, rfl⟩
    have hvEq : T.vertex hia = A.vertex iA := by
      rw [← hcast]
      exact hA.2.1 iA
    rw [hvEq]
    exact TreeSequenceInitialSegmentVertexSetSubset hAB hvA
  have hvB : T.vertex hib ∈ TreeSequenceVertexSet B := by
    have hibBound : hib.val < B.length + 1 := by
      have h := hlenB
      clear * - h hibLt
      omega
    let iB : Fin (B.length + 1) := ⟨hib.val, hibBound⟩
    have hcast : Fin.castLE (Nat.succ_le_succ hBprefix.1) iB = hib := Fin.ext rfl
    have hvEq : T.vertex hib = B.vertex iB := by
      rw [← hcast]
      exact hBprefix.2.1 iB
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨iB, hvEq.symm⟩
  have hwu : T.vertex (Fin.last T.length) ≠ T.vertex hia := by
    intro heq
    have hidx := T.vertex_injective heq
    have hval := congrArg Fin.val hidx
    simp only [Fin.val_last] at hval
    omega
  have hwv : T.vertex (Fin.last T.length) ≠ T.vertex hib := by
    intro heq
    have hidx := T.vertex_injective heq
    have hval := congrArg Fin.val hidx
    simp only [Fin.val_last] at hval
    omega
  have hterminalPath :=
    P2905_T2_ElementaryTerminalComponent G phi alpha beta hne ctx.proper
      (TreeSequenceVertexSet B) hElem
      (T.vertex hia) (T.vertex hib) (T.vertex (Fin.last T.length))
      huB hvB hwu hwv hAlphaFirst hbetaFirst (Or.inl hterminal) hSame
  let sigma := TwoColorComponentSwap G phi alpha beta
      (Sum.inl (T.vertex (Fin.last T.length)))
  have hsigma : sigma = TwoColorComponentSwap G phi alpha beta
      (Sum.inl (T.vertex (Fin.last T.length))) := rfl
  have hswapMissing := TwoColorComponentSwapMissingBehavior
    G phi alpha beta hne ctx.proper (Sum.inl (T.vertex (Fin.last T.length)))
  have hbetaTerminal : beta ∈ MissingColors G sigma (T.vertex (Fin.last T.length)) := by
    exact hswapMissing.2.1 _ rfl hterminal
  have hbetaX : beta ∈ TreeMissingColors sigma X := by
    obtain ⟨v, hv, hmiss⟩ := Finset.mem_biUnion.mp hbX
    have hvB' : v ∈ TreeSequenceVertexSet B := TreeSequenceInitialSegmentVertexSetSubset hXB hv
    have heq := hterminalPath.2.2 v hvB'
    exact Finset.mem_biUnion.mpr ⟨v, hv, heq ▸ hmiss⟩
  have hmissingPrefix :
      alpha ∈ TreeMissingColors phi B ∧ beta ∈ TreeMissingColors phi B := ⟨haB, hbB⟩
  have hcase :
      (0 < H.dividerCount ∧
        alpha ∈ TreeMissingColors phi (H.stage ⟨H.dividerCount, by omega⟩)) ∨
      (H.dividerCount = 0 ∧
        (alpha ∈ TreeMissingColors phi Tn ∨
          (alpha ∈ TreeMissingColors phi A ∧ alpha ∉
            TashkinovStoredColors ett.series.data (Fin.last ett.rounds) ∧
            beta ∉ TashkinovStoredColors ett.series.data (Fin.last ett.rounds)))) := by
    by_cases hd : 0 < H.dividerCount
    · left
      refine ⟨hd, ?_⟩
      let r : Fin H.dividerCount := ⟨H.dividerCount - 1, by omega⟩
      have hq : q = r.succ := by
        apply Fin.ext
        simp [q, r]
        omega
      have hm := hStageMiss
      unfold HierarchyStageMissingColors at hm
      rw [hq] at hm
      change alpha ∈ TreeMissingColors phi (H.stage r.succ.castSucc) at hm
      have hidx : r.succ.castSucc = ⟨H.dividerCount, by omega⟩ := by
        apply Fin.ext
        simp [r]
        omega
      simpa only [hidx] using hm
    · have hz : H.dividerCount = 0 := by omega
      right
      refine ⟨hz, Or.inl ?_⟩
      have hq : q = 0 := Fin.ext (by simp [q, hz])
      have hm := hStageMiss
      unfold HierarchyStageMissingColors at hm
      rw [hq] at hm
      simpa [Tn] using hm
  have hcut : A.length + (ell - 2) = T.length - 2 := by
    rw [hell]
    have ha : A.length ≤ T.length := hA.1
    have ht : 3 ≤ T.length - A.length := htailA
    clear * - ha ht
    omega
  have htailEdges : ∀ r : Fin T.length, A.length ≤ r.val →
      sigma (T.edge r) = phi (T.edge r) := by
    intro r hr
    have hnotAlpha := hAlphaAvoid r hr
    have hnotBeta : phi (T.edge r) ≠ some beta := by
      intro hc
      by_cases hbefore : r.val < X.length
      · apply hbU
        simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨r, hr, ?_, hc⟩
        rw [hlenX] at hbefore
        omega
      · apply hbN
        exact hSuffixN beta r (by omega) hc
    simp [sigma, TwoColorComponentSwap, hnotAlpha, hnotBeta]
  have vertexMemB (i : Fin (T.length + 1)) (hi : i.val < T.length) :
      T.vertex i ∈ TreeSequenceVertexSet B := by
    have hbnd : i.val < B.length + 1 := by
      have h := hlenB
      clear * - h hi
      omega
    let j : Fin (B.length + 1) := ⟨i.val, hbnd⟩
    have hcast : Fin.castLE (Nat.succ_le_succ hBprefix.1) j = i := Fin.ext rfl
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨j, ?_⟩
    have hvEq : T.vertex i = B.vertex j := by
      rw [← hcast]
      exact hBprefix.2.1 j
    exact hvEq.symm
  have firstLeFor (psi : PartialEdgeColoring E k) (c : Fin k)
      (i : Fin (T.length + 1))
      (hi : c ∈ MissingColors G psi (T.vertex i)) :
      (HierarchyFirstMissingPosition psi T c).val ≤ i.val := by
    let candidates := Finset.univ.filter fun j : Fin (T.length + 1) =>
      c ∈ MissingColors G psi (T.vertex j)
    have hm : i ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    have hn : candidates.Nonempty := ⟨i, hm⟩
    unfold HierarchyFirstMissingPosition
    rw [dif_pos hn]
    have hle := Finset.min'_le candidates i hm
    change (candidates.min' hn).val ≤ i.val at hle
    exact hle
  have firstMemFor (psi : PartialEdgeColoring E k) (c : Fin k)
      (hlt : (HierarchyFirstMissingPosition psi T c).val < T.length) :
      c ∈ MissingColors G psi (T.vertex (HierarchyFirstMissingPosition psi T c)) := by
    let candidates := Finset.univ.filter fun j : Fin (T.length + 1) =>
      c ∈ MissingColors G psi (T.vertex j)
    by_cases hn : candidates.Nonempty
    · unfold HierarchyFirstMissingPosition
      rw [dif_pos hn]
      exact (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
    · have hh : (HierarchyFirstMissingPosition psi T c).val = T.length := by
        unfold HierarchyFirstMissingPosition
        rw [dif_neg hn]
        rfl
      omega
  have missingAtB (i : Fin (T.length + 1)) (hi : i.val < T.length) :
      MissingColors G sigma (T.vertex i) = MissingColors G phi (T.vertex i) :=
    hterminalPath.2.2 (T.vertex i) (vertexMemB i hi)
  have firstPosEq (c : Fin k) :
      HierarchyFirstMissingPosition sigma T c =
        HierarchyFirstMissingPosition phi T c := by
    let ps := HierarchyFirstMissingPosition sigma T c
    let po := HierarchyFirstMissingPosition phi T c
    by_cases hEarly : po.val < T.length
    · have hmissOld := firstMemFor phi c hEarly
      have hmissNew : c ∈ MissingColors G sigma (T.vertex po) := by
        rw [missingAtB po hEarly]
        exact hmissOld
      have hleNew := firstLeFor sigma c po hmissNew
      by_cases hNewEarly : ps.val < T.length
      · have hmissNewFirst := firstMemFor sigma c hNewEarly
        have hmissOldFirst : c ∈ MissingColors G phi (T.vertex ps) := by
          rw [← missingAtB ps hNewEarly]
          exact hmissNewFirst
        have hleOld := firstLeFor phi c ps hmissOldFirst
        apply Fin.ext
        omega
      · have hNewLast : ps.val = T.length := by
          have hlt := ps.isLt
          omega
        have hltOld : po.val < T.length := hEarly
        have hleNew' : ps.val ≤ po.val := hleNew
        omega
    · have hOldLast : po.val = T.length := by
        have hlt := po.isLt
        omega
      by_cases hNewEarly : ps.val < T.length
      · have hmissNewFirst := firstMemFor sigma c hNewEarly
        have hmissOldFirst : c ∈ MissingColors G phi (T.vertex ps) := by
          rw [← missingAtB ps hNewEarly]
          exact hmissNewFirst
        have hleOld := firstLeFor phi c ps hmissOldFirst
        omega
      · have hNewLast : ps.val = T.length := by
          have hlt := ps.isLt
          omega
        apply Fin.ext
        omega
  have hstoredFirst :
      ∀ rho, rho ∈ D →
        HierarchyFirstMissingPosition sigma T rho =
          HierarchyFirstMissingPosition phi T rho := by
    intro rho _
    exact firstPosEq rho
  have hstable := StableChangeCasesOneTwoFullTail G k e0 input T phi ett
    base C ctx alpha beta hne hmissingPrefix
    (Sum.inl (T.vertex (Fin.last T.length))) hterminalPath.2.1 sigma rfl hcase
    hterminalPath.1 htailEdges hterminalPath.2.2 hstoredFirst
  rcases hstable with ⟨_, _, _, _, hCorr⟩
  obtain ⟨corr, hmax, baseT, K, goodT, sameGood⟩ := hCorr
  have seriesFacts : ∀ j : Fin (ett.rounds + 1),
      IsProperEdgeColoring G (ett.series.data.coloring j) ∧
        IsOneEdgeUncolored (ett.series.data.coloring j) e0 := by
    clear * - G ett e0
    intro j
    have certificate := ett.series.certified j
    cases certificate with
    | initial triple seedLength initialColoring initialStored initialEdges initialKind
        initialVertex initialOutside initialDelta initialGamma initialClosure =>
        simpa [initialColoring] using triple.2.2.2
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
        rw [currentColoring]
        exact ⟨choice.selectedProper, choice.selectedOneUncolored⟩
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper secondStableOneUncolored
        secondStableRelation exitWitness currentColoring currentProper
        currentOneUncolored currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma closedExtension orderedExtension
        strictExtension =>
        exact ⟨currentProper, currentOneUncolored⟩
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored currentEdges
        currentKind currentVertex currentOutside currentDelta currentGamma adjoined
        adjoinedExactly closedExtension orderedExtension strictExtension =>
        rw [currentColoring]
        exact ⟨previousProper, previousOneUncolored⟩
  let corrRefl : CorrespondingExtendedTashkinovTree G k e0 ett phi T :=
    { replacementInput := input
      replacementSeries := ett.series
      replacementETT := ett
      rungAgreement := rfl
      seriesPresentation := HEq.rfl
      finalGeneratingColoring := ett.generatingColoring
      ladderTreesAgree := fun _ => rfl
      storedColorsAgree := fun _ => rfl
      connectingEdgesAgree := fun _ => rfl
      extensionKindsAgree := fun _ => rfl
      replacementProper := fun j => (seriesFacts j).1
      replacementOneUncolored := fun j => (seriesFacts j).2
      replacementStable := fun _ => ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩ }
  let PRefl : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx :=
    { coloring := phi
      corresponding := corrRefl
      maximum := C.maximum
      replacementBase := base
      counterexample := C
      sameGood := ⟨⟨rfl, rfl, HEq.rfl, HEq.rfl, Iff.rfl, fun _ => rfl⟩,
        rfl, fun _ => ⟨rfl, fun _ _ => rfl⟩⟩
      minimumContext := ctx }
  have hVpair : ∃ v ∈ TreeSequenceVertexSet T,
      beta ∈ MissingColors G sigma v ∧ v ≠ T.vertex (Fin.last T.length) := by
    obtain ⟨v, hv, hmiss⟩ := Finset.mem_biUnion.mp hbetaX
    obtain ⟨i, hi⟩ : ∃ i : Fin (X.length + 1), X.vertex i = v := by
      simpa only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] using hv
    let j : Fin (T.length + 1) := Fin.castLE (Nat.succ_le_succ hXprefix.1) i
    have hvT : v = T.vertex j := by
      rw [← hi]
      exact hXprefix.2.1 i
    have hjval : j.val = i.val := rfl
    have hiLE : i.val ≤ X.length := by
      have hiLt := i.isLt
      omega
    have hilen : i.val ≤ T.length - 2 := hiLE.trans_eq hlenX
    have hjlt : j.val < T.length := by
      rw [hjval]
      have hlen : T.length - 2 < T.length := by omega
      exact Nat.lt_of_le_of_lt hilen hlen
    refine ⟨v, ?_, hmiss, ?_⟩
    · rw [hvT]
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨j, rfl⟩
    · intro heq
      have hidx := T.vertex_injective (hvT.symm.trans heq)
      have hval := congrArg Fin.val hidx
      simp only [Fin.val_last] at hval
      omega
  let Cnew : HierarchyCounterexample baseT :=
    { positive := by rw [corr.rungAgreement]; exact C.positive
      hierarchy := K
      good := goodT
      maximum := hmax
      notElementary := by
        intro he
        obtain ⟨v, hv, hmissV, hneV⟩ := hVpair
        have hterm : T.vertex (Fin.last T.length) ∈ TreeSequenceVertexSet T := by
          simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨Fin.last T.length, rfl⟩
        have hdisj := Finset.disjoint_left.mp (he hv hterm hneV)
        exact hdisj hmissV hbetaTerminal }
  obtain ⟨P, hP⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi
    ett base C ctx PRefl sigma corr baseT Cnew sameGood
  have terminalTreeOf (rho : PartialEdgeColoring E k)
      (c : CorrespondingExtendedTashkinovTree G k e0 ett rho T) :
      c.replacementETT.series.data.tree
        (Fin.last c.replacementETT.rounds).castSucc = Tn := by
    rcases c with ⟨replacementInput, replacementSeries, replacementETT,
      rungAgreement, seriesPresentation, finalGeneratingColoring,
      ladderTreesAgree, storedColorsAgree, connectingEdgesAgree,
      extensionKindsAgree, replacementProper, replacementOneUncolored,
      replacementStable⟩
    cases replacementETT with
    | mk rounds roundsPositive series above strict below generating =>
      cases rungAgreement
      have hseries : series = replacementSeries := eq_of_heq seriesPresentation
      cases hseries
      let i : Fin ett.rounds :=
        ⟨ett.rounds - 1, by have hp := ett.roundsPositive; omega⟩
      have hi : i.succ = Fin.last ett.rounds := by
        apply Fin.ext
        change ett.rounds - 1 + 1 = ett.rounds
        exact Nat.sub_add_cancel ett.roundsPositive
      simpa [Tn, hi] using ladderTreesAgree i
  have hterminalTree := terminalTreeOf P.coloring P.corresponding
  have hcoreEq : base.core = P.replacementBase.core := P.sameGood.1.1
  have hcount : H.dividerCount = P.counterexample.hierarchy.dividerCount :=
    P.sameGood.2.choose
  let qNew : Fin (P.counterexample.hierarchy.dividerCount + 1) :=
    Fin.last P.counterexample.hierarchy.dividerCount
  have hqCast : Fin.cast (congrArg (fun n => n + 1) hcount) q = qNew := by
    apply Fin.ext
    simp [qNew, q]
  have hsg := P.sameGood.2.choose_spec q
  have hD : HierarchyStoredColorsAt P.counterexample.hierarchy qNew = D := by
    have h := hsg.1
    rw [hqCast] at h
    exact h.symm
  have hGammaEq (rho : Fin k) (hrho : rho ∈ D) :
      C.good.gamma q rho = P.counterexample.good.gamma qNew rho := by
    have h := hsg.2 rho hrho
    rw [hqCast] at h
    exact h
  refine ⟨P, beta, ?_, ?_, ?_⟩
  · rw [hP]
    exact hbetaTerminal
  · rw [hP]
    exact hbetaX
  · change beta ∉
      (HierarchyStoredColorsAt P.counterexample.hierarchy qNew).biUnion
          (P.counterexample.good.gamma qNew) ∪
        ((TreeSequenceVertexSet P.replacementBase.core \
            TreeSequenceVertexSet
              (P.corresponding.replacementETT.series.data.tree
                (Fin.last P.corresponding.replacementETT.rounds).castSucc)).biUnion
          fun v => MissingColors G P.coloring v)
    intro hbad
    rcases Finset.mem_union.mp hbad with hGammaNew | hMnew
    · obtain ⟨rho, hrho, hbetaGammaNew⟩ := Finset.mem_biUnion.mp hGammaNew
      have hrhoOld : rho ∈ D := by rw [← hD]; exact hrho
      have hbetaGammaOld : beta ∈ C.good.gamma q rho := by
        rw [hGammaEq rho hrhoOld]
        exact hbetaGammaNew
      exact hbGamma (Finset.mem_biUnion.mpr ⟨rho, hrhoOld, hbetaGammaOld⟩)
    · obtain ⟨v, hv, hbetaV⟩ := Finset.mem_biUnion.mp hMnew
      obtain ⟨hvCoreNew, hvNotTnew⟩ := Finset.mem_sdiff.mp hv
      have hvCoreOld : v ∈ TreeSequenceVertexSet base.core := by
        rw [hcoreEq]
        exact hvCoreNew
      have hvNotTn : v ∉ TreeSequenceVertexSet Tn := by
        intro hvTn
        apply hvNotTnew
        rw [hterminalTree]
        exact hvTn
      have hvB : v ∈ TreeSequenceVertexSet B := hcoreB hvCoreOld
      have hbetaPhi : beta ∈ MissingColors G phi v := by
        rw [hP] at hbetaV
        rw [hterminalPath.2.2 v hvB] at hbetaV
        exact hbetaV
      have hbetaM0 : beta ∈ M0 :=
        Finset.mem_biUnion.mpr
          ⟨v, Finset.mem_sdiff.mpr ⟨hvCoreOld, hvNotTn⟩, hbetaPhi⟩
      exact hbM0 hbetaM0
